import Mathlib.Data.Set.Basic
/-! # 群論 解答 -/
namespace myGroup

section

--  1. 群

class Group (G : Type*) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : G, mul one a = a
  inv_mul_cancel : ∀ a : G, mul (inv a) a = one
variable {G G' : Type*} [Group G] [Group G']
instance : Mul G where mul := Group.mul
instance : One G where one := Group.one
instance : Inv G where inv := Group.inv

theorem mul_assoc : ∀ a b c : G, a * b * c = a * (b * c) := Group.mul_assoc
@[simp] theorem one_mul : ∀ a : G, 1 * a = a := Group.one_mul
@[simp] theorem inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1 := Group.inv_mul_cancel

@[simp] theorem mul_inv_cancel : ∀ a : G, a * a⁻¹ = 1 := by
  intro a
  conv =>
    lhs
    arg 1
    rw [← one_mul a, ← inv_mul_cancel a⁻¹, mul_assoc]
  simp [mul_assoc]
@[simp] theorem mul_one : ∀ a : G, a * 1 = a := by
  intro a
  rw [← inv_mul_cancel a, ← mul_assoc]
  simp

theorem left_one_unique : ∀ a b : G, a * b = b → a = 1 := by
  intro a b h
  have : a * b * b⁻¹ = b * b⁻¹ := by congr
  simp [mul_assoc] at this
  assumption
theorem right_one_unique : ∀ a b : G, a * b = a → b = 1 := by
  intro a b h
  have : a⁻¹ * (a * b) = a⁻¹ * a := by congr
  simp [← mul_assoc] at this
  assumption
theorem left_inv_unique : ∀ a b : G, a * b = 1 → a = b⁻¹ := by
  intro a b h
  rw [← mul_one a, ← mul_inv_cancel b, ← mul_assoc, h, one_mul]
theorem right_inv_unique : ∀ a b : G, a * b = 1 → b = a⁻¹ := by
  intro a b h
  rw [← one_mul b, ← inv_mul_cancel a, mul_assoc, h, mul_one]

@[simp] theorem inv_inv : ∀ a : G, a⁻¹⁻¹ = a := by
  intro a
  exact eq_comm.mp (left_inv_unique a (a⁻¹) (mul_inv_cancel a))
@[simp] theorem mul_inv : ∀ a b : G, (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  intro a b
  apply eq_comm.mp (right_inv_unique (a * b) (b⁻¹ * a⁻¹) ?_)
  rw [← mul_assoc, mul_assoc a]
  simp
@[simp] theorem one_inv : (1 : G)⁻¹ = 1 := by
  rw [← one_mul 1⁻¹, mul_inv_cancel]

--  2. 部分群

class Subgroup (H : Set G) where
  one_mem : 1 ∈ H
  mul_mem : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H
  inv_mem : ∀ a ∈ H, a⁻¹ ∈ H
variable {H : Set G} [Subgroup H]

theorem one_mem : (1 : G) ∈ H := Subgroup.one_mem
theorem mul_mem : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H := Subgroup.mul_mem
theorem inv_mem : ∀ a ∈ H, a⁻¹ ∈ H := Subgroup.inv_mem

class Normal (N : Set G) extends Subgroup N where
  conj_mem : ∀ n ∈ N, ∀ g : G, g * n * g⁻¹ ∈ N
variable {N : Set G} [Normal N]

theorem conj_mem : ∀ n ∈ N, ∀ g : G, g * n * g⁻¹ ∈ N := Normal.conj_mem

theorem Normal_mem_mul : ∀ n ∈ N, ∀ a : G, ∃ m ∈ N, n * a = a * m  := by
  intro n hn a
  use (a⁻¹ * n * a)
  constructor
  · have := conj_mem n hn a⁻¹
    rwa [inv_inv] at this
  · simp [← mul_assoc]

--  3. 剰余類

def leftRel (H : Set G) [Subgroup H] : G → G → Prop := fun a b => b⁻¹ * a ∈ H
@[simp] theorem leftRel_iff (H : Set G) [Subgroup H] : ∀ a b : G, leftRel H a b ↔ b⁻¹ * a ∈ H := by
  intros
  rfl

theorem leftRel_refl : ∀ x : G, leftRel H x x := by
  intro x
  simp [one_mem]
theorem leftRel_symm : ∀ x y : G, leftRel H x y → leftRel H y x := by
  intro x y h
  have := inv_mem (y⁻¹ * x) h
  rwa [mul_inv, inv_inv] at this
theorem leftRel_trans : ∀ x y z : G, leftRel H x y → leftRel H y z → leftRel H x z := by
  intro x y z hxy hyz
  have := mul_mem (z⁻¹ * y) hyz (y⁻¹ * x) hxy
  rwa [mul_assoc, ← mul_assoc y, mul_inv_cancel, one_mul] at this

def leftSetoid (H : Set G) [Subgroup H] : Setoid G where
  r := leftRel H
  iseqv := {
    refl := leftRel_refl
    symm := by
      intro x y h
      exact leftRel_symm x y h
    trans := by
      intro x y z hxy hyz
      exact leftRel_trans x y z hxy hyz
    }
def leftCoset (G : Type*) [Group G] (H : Set G) [Subgroup H] := Quotient (leftSetoid H)
infix:30 " ⧸ " => leftCoset
notation:70 a " • " H => Quotient.mk (leftSetoid H) a

--  4. 商群

theorem well_defined_mul {a a' b b' : G} : leftRel N a b →
    leftRel N a' b' → leftRel N (a * a') (b * b') := by
  simp only [leftRel_iff, mul_inv]
  intro h h'
  rw [mul_assoc, ← mul_assoc b⁻¹]
  apply Exists.elim (Normal_mem_mul (b⁻¹ * a) h a')
  intro n ⟨hn, heq⟩
  rw [heq, ← mul_assoc]
  exact mul_mem (b'⁻¹ * a') h' n hn
theorem well_defined_inv {a b : G} : leftRel N a b → leftRel N a⁻¹ b⁻¹ := by
  intro h1
  rw [leftRel_iff, ← mul_inv]
  have h2 := conj_mem (b⁻¹ * a) h1 b
  rw [← mul_assoc, mul_inv_cancel, one_mul] at h2
  exact inv_mem (a * b⁻¹) h2

def mul_to_quot : G → G → G ⧸ N := fun a b => Quotient.mk (leftSetoid N) (a * b)
def inv_to_quot : G → G ⧸ N := fun a => Quotient.mk (leftSetoid N) a⁻¹
def QuotientGroup_mul_def : G ⧸ N → G ⧸ N → G ⧸ N := Quotient.lift₂ mul_to_quot (by
  intro _ _ _ _ h h'
  exact Quotient.eq.mpr (well_defined_mul h h'))
def QuotientGroup_inv_def : G ⧸ N → G ⧸ N := Quotient.lift inv_to_quot (by
  intro _ _ h
  exact Quotient.eq.mpr (well_defined_inv h))
infixl:60 " * " => QuotientGroup_mul_def
notation:80 a "⁻¹ " => QuotientGroup_inv_def a

@[simp] theorem QuotientGroup_mul (a b : G) : (a • N) * (b • N) = (a * b) • N := rfl
@[simp] theorem QuotientGroup_inv (a : G) : (a • N)⁻¹ = a⁻¹ • N := rfl

instance : Group (G ⧸ N) where
  mul := QuotientGroup_mul_def
  one := (1 : G) • N
  inv := QuotientGroup_inv_def
  mul_assoc := by
    intro a b c
    induction a using Quotient.ind
    induction b using Quotient.ind
    induction c using Quotient.ind
    simp [mul_assoc]
    rfl
  one_mul := by
    intro a
    induction a using Quotient.ind
    simp
    rfl
  inv_mul_cancel := by
    intro a
    induction a using Quotient.ind
    simp
    rfl

--  5. 準同型写像

class GroupHom (f : G → G') where
  mul_hom : ∀ a b : G, f (a * b) = f a * f b
variable (f : G → G') [GroupHom f]

set_option warning.simp.varHead false
@[simp] theorem mul_hom : ∀ a b : G, f (a * b) = f a * f b := GroupHom.mul_hom
@[simp] theorem map_one : f 1 = 1 := by
  apply left_one_unique (f 1) (f 1)
  rw [← mul_hom, one_mul]
@[simp] theorem map_inv : ∀ a : G, f a⁻¹ = (f a)⁻¹ := by
  intro a
  apply left_inv_unique (f a⁻¹) (f a)
  rw [← mul_hom, inv_mul_cancel, map_one f]

def ker (f : G → G') [GroupHom f] : Set G := {a : G | f a = 1}
theorem in_ker_iff_eq_one : ∀ a : G, a ∈ (ker f) ↔ f a = 1 := by
  intros
  rfl
instance : Normal (ker f) where
  one_mem := (in_ker_iff_eq_one f 1).mpr (map_one f)
  mul_mem := by
    simp only [in_ker_iff_eq_one]
    intro _ ha _ hb
    simp [ha, hb]
  inv_mem := by
    simp only [in_ker_iff_eq_one]
    intro _ ha
    simp [ha]
  conj_mem := by
    simp only [in_ker_iff_eq_one]
    intro _ hn _
    simp [hn]

--  6. 準同型定理

def InducedFunction : G ⧸ ker f → G' := Quotient.lift f (by
  intro a b hab
  have h : f (b⁻¹ * a) = 1 := (in_ker_iff_eq_one f (b⁻¹ * a)).mp hab
  rw [mul_hom f, map_inv f] at h
  rw [← inv_inv (f b)]
  exact right_inv_unique (f b)⁻¹ (f a) h)
@[simp] theorem IndFunct_eq : ∀ a : G, InducedFunction f (a • ker f) = f a := by
  intros
  rfl
instance : GroupHom (InducedFunction f) where
  mul_hom := by
    intro a b
    induction a using Quotient.ind
    induction b using Quotient.ind
    simp only [IndFunct_eq]
    rw [← mul_hom f]
    rfl

theorem Bij_of_IndFunct (f_surj : Function.Surjective f) :
    Function.Bijective (InducedFunction f) ∧ (InducedFunction f) ∘ (fun a => a • ker f) = f := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro a b h
    induction a using Quotient.ind
    induction b using Quotient.ind
    rename_i a b
    simp only [IndFunct_eq] at h
    rw [Quotient.eq.mpr]
    suffices b⁻¹ * a ∈ ker f from this
    simp [in_ker_iff_eq_one f, h]
  · intro b
    cases f_surj b with | intro a h =>
    use a • ker f
    simp [h]
  · funext
    exact Function.comp_apply

end

variable {G G' : Type*} [Group G] [Group G']
variable {H N : Set G} [Subgroup H] [Normal N]
variable {f : G → G'} [GroupHom f]

--  問1

structure inv_mul_in_Set (S : Set G) where
  exists_mem : ∃ a₀ : G, a₀ ∈ S
  inv_mul : ∀ a ∈ S, ∀ b ∈ S, a⁻¹ * b ∈ S

variable {S : Set G}
theorem inv_mul_in_Set_one_mem (hS : inv_mul_in_Set S) : (1 : G) ∈ S := by
  cases hS.exists_mem with | intro a ha =>
  have h :=  hS.inv_mul a ha a ha
  rwa [inv_mul_cancel a] at h
theorem inv_mul_in_Set_inv_mem (hS : inv_mul_in_Set S) : ∀ a ∈ S, a⁻¹ ∈ S := by
  intro a ha
  have h := hS.inv_mul a ha 1 (inv_mul_in_Set_one_mem hS)
  rwa [mul_one] at h
theorem inv_mul_in_Set_mul_mem (hS : inv_mul_in_Set S) :
    ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S := by
  intro a ha b hb
  have h := hS.inv_mul a⁻¹ (inv_mul_in_Set_inv_mem hS a ha) b hb
  rwa [inv_inv] at h

example (hS : inv_mul_in_Set S) : Subgroup S where
  one_mem := inv_mul_in_Set_one_mem hS
  mul_mem := inv_mul_in_Set_mul_mem hS
  inv_mem := inv_mul_in_Set_inv_mem hS

--  問2

def Center (G : Type*) [Group G] : Set G := {a | ∀ x : G, a * x = x * a}

example : Normal (Center G) where
  one_mem := by
    simp [Center]
  mul_mem := by
    intro a ha b hb x
    rw [mul_assoc, hb x, ← mul_assoc, ha x, mul_assoc]
  inv_mem := by
    intro a h x
    rw [← inv_inv x, ← mul_inv, ← mul_inv]
    exact congr rfl (eq_comm.mp (h x⁻¹))
  conj_mem := by
    intro n h g x
    rw [eq_comm.mp (h g), mul_assoc n]
    simp_all [Center]

--  問3

def set_mul (S T : Set G) : Set G := {x | ∃ s ∈ S, ∃ t ∈ T, x = s * t}

example : Subgroup (set_mul H N) where
  one_mem := by
    refine Exists.intro 1 ⟨one_mem, Exists.intro 1 ⟨one_mem, ?_⟩⟩
    rw [one_mul]
  mul_mem := by
    intro a ha b hb
    cases ha with | intro a1 ha1 =>
    cases ha1.right with | intro a2 ha2 =>
    cases hb with | intro b1 hb1 =>
    cases hb1.right with | intro b2 hb2 =>
    cases Normal_mem_mul a2 ha2.left b1 with | intro n hn =>
    refine Exists.intro (a1 * b1) ⟨mul_mem a1 ha1.left b1 hb1.left, ?_⟩
    refine Exists.intro (n * b2) ⟨mul_mem n hn.left b2 hb2.left, ?_⟩
    rw [ha2.right, hb2.right, mul_assoc, ← mul_assoc a2, hn.right]
    simp only [mul_assoc]
  inv_mem := by
    intro a ha
    cases ha with | intro h hh =>
    cases hh.right with | intro n hn =>
    cases Normal_mem_mul n⁻¹ (inv_mem n hn.left) h⁻¹ with | intro m hm =>
    refine Exists.intro h⁻¹ ⟨inv_mem h hh.left, ?_⟩
    refine Exists.intro m ⟨hm.left, ?_⟩
    rw [hn.right, mul_inv, hm.right]

--  問4

def conjugacy (a b : G) : Prop := ∃ x : G, (x * a) * x⁻¹ = b

example : Setoid G where
  r := conjugacy
  iseqv := {
    refl := by
      intro x
      use 1
      simp
    symm := by
      intro x y h
      cases h with | intro z h =>
      use z⁻¹
      rw [eq_comm.mp h, mul_assoc, mul_assoc, ← mul_assoc, ← mul_assoc z⁻¹]
      simp
    trans := by
      intro x y z h1 h2
      cases h1 with | intro v hv =>
      cases h2 with | intro w hw =>
      use w * v
      rw [mul_inv, ← mul_assoc, mul_assoc w, mul_assoc w, hv, hw]
    }

--  問5

example : Function.Injective f ↔ ∀ a : G, f a = 1 → a = 1 := by
  constructor
  · intro hf a hfa
    rw [← map_one f] at hfa
    exact hf hfa
  · intro h x y hf
    rw [← inv_inv y]
    refine left_inv_unique x y⁻¹ (h _ ?_)
    simp [hf]

--  問6

example (hf : Function.Bijective f) : GroupHom (Function.surjInv hf.surjective) where
  mul_hom := by
    intro a' b'
    apply hf.left
    simp [Function.surjInv_eq]

--  問7

example : Subgroup (Set.range f) where
  one_mem := by
    exact Exists.intro 1 (map_one f)
  mul_mem := by
    intro a' ha' b' hb'
    cases ha' with | intro a ha =>
    cases hb' with | intro b hb =>
    use (a * b)
    simp [ha, hb]
  inv_mem := by
    intro a' h'
    cases h' with | intro a h =>
    use a⁻¹
    simp [h]

--  問8

variable {G1 G2 : Type*} [Group G1] [Group G2]

instance : Group (Prod G1 G2) where
  mul a b := ⟨a.fst * b.fst, a.snd * b.snd⟩
  one := ⟨1, 1⟩
  inv a := ⟨a.fst⁻¹, a.snd⁻¹⟩
  mul_assoc := by
    intros
    simp [mul_assoc]
  one_mul := by
    simp
  inv_mul_cancel := by
    simp

@[simp] theorem Prod_mul : ∀ a b : Prod G1 G2, a * b = ⟨a.fst * b.fst, a.snd * b.snd⟩ := by
  intros
  rfl
@[simp] theorem Prod_inv : ∀ a : Prod G1 G2, a⁻¹ = ⟨(a.fst)⁻¹, (a.snd)⁻¹⟩ := by
  intros
  rfl

theorem univ_of_GroupProd (f1 : G → G1) [GroupHom f1] (f2 : G → G2) [GroupHom f2] :
    ∃! f : G → Prod G1 G2, GroupHom f ∧
    (fun a => a.fst) ∘ f = f1 ∧ (fun a => a.snd) ∘ f = f2 := by
  use (fun x => ⟨f1 x, f2 x⟩)
  refine ⟨⟨{mul_hom := ?_}, ⟨?_, ?_⟩⟩, ?unique⟩
  case unique =>
    intro f ⟨_, ⟨hf1, hf2⟩⟩
    simp [eq_comm.mp hf1, eq_comm.mp hf2]
  all_goals funext
  all_goals simp

--  問9

variable (N' : Set G') [Normal N']

example : Normal (f⁻¹' N') where
  one_mem := by
    simp [one_mem]
  mul_mem := by
    intro a ha b hb
    simp_all [mul_mem]
  inv_mem := by
    intro a h
    simp_all [inv_mem]
  conj_mem := by
    intro n hn g
    simp_all [conj_mem]

end myGroup
