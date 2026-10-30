-- A.1 def, let（p.41）
-- 自然数を受け取り、それを 2 倍した値を返す関数 double を定義する
def double (a : Nat) : Nat := a * 2
-- 文字列 Hello を hello という名前で定義
def hello : String := "Hello"

-- 多くの場合で型は本体から推論できるので省略可能
def plus_one (a : Nat) := a + 1 -- : Nat を省略している
def pi := 3.141592

def sumExample : Nat :=
  let a := 3
  let b := 5
  a + b

-- A.2 structure, ⟨ ⟩（p.41–42）
-- さまざまな型が入る 2 次元の点の座標を格納する構造体をつくる
structure Point2D (α : Type) where
  x : α
  y : α

-- Point2D に z 座標のみ加えて 3D にできるので、Point2D をベースに Point3D を作成する
structure Point3D (α : Type) extends Point2D α where
  z : α

-- (10,20,30) という点を作る
def p : Point3D Nat := {x := 10, y := 20, z := 30}
#eval p.z -- 30

-- 本文中の無名コンストラクタの使用例
def q : Point2D Nat := ⟨10, 20⟩

-- A.3 class, instance（p.42）
-- 足し算を定義する
class Plus (α : Type) where
  plus : α → α → α

-- Nat(自然数) で Plus ができることを Lean 4 に教える
instance : Plus Nat where
  plus := Nat.add -- Nat.add は自然数にあらかじめ用意されている足し算

-- String(文字列) でも Plus を文字列の連結として定義する
instance : Plus String where
  plus := String.append

-- A.4 abbrev, variable（p.43）
abbrev Str := String

def greeting : Str := "Hello"

abbrev twice := fun (n : Nat) => n * 2
#eval twice 5 -- 10

-- 本文中の def n との衝突を避けるため、この例だけ section 内に置く
section VariableExamples

-- 以降 n は自然数とする
variable (n : Nat)

-- (n : Nat) を毎回書かなくてよい
example : n + 0 = n := by
  rfl

example : 0 + n = n := by
  exact Nat.zero_add n

end VariableExamples

-- A.5 infix, infixl, infixr, prefix（p.44）
def plus (a b : Nat) : Nat := a + b
#eval plus 2 3 -- 5

infixl:65 " +++ " => plus
#eval 2 +++ 3 -- 5

def doubleAgain (n : Nat) : Nat := n * 2
prefix:100 "dbl " => doubleAgain
#eval dbl 5 -- 10

-- A.6 notation（p.44）
def square (n : Nat) : Nat := n * n
notation "sq[" n "]" => square n
#eval sq[5] -- 25

-- A.7 inductive（p.45）
inductive MyBool where
  | true
  | false

inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

def myZero : MyNat := MyNat.zero
def myOne : MyNat := MyNat.succ MyNat.zero
def myTwo : MyNat := MyNat.succ myOne

-- A.8 theorem の発展（p.45–47）
theorem add_zero_example (n : Nat) :
    n + 0 = n := by
  rfl

example : 5 + 0 = 5 := by
  exact add_zero_example 5

theorem add_zero_implicit {n : Nat} :
    n + 0 = n := by
  rfl

example : 5 + 0 = 5 := by
  exact add_zero_implicit

example : 5 + 0 = 5 := by
  exact add_zero_implicit (n := 5)

theorem my_refl {α : Type} (a : α) :
    a = a := by
  rfl

example : 3 = 3 := by
  exact my_refl 3

example : "Hello" = "Hello" := by
  exact my_refl "Hello"

def combine {α : Type} [Plus α]
    (a b : α) : α :=
  Plus.plus a b