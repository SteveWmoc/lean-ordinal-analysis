import OrdinalAnalysis.Epsilon0.MathlibOrderIso

/-!
# Notation-level arithmetic below ε₀

Mathlib's `NONote` already implements executable ordinal addition,
subtraction, multiplication, and exponentiation on canonical ε₀ notations,
together with semantic correctness theorems.

Rather than duplicate those algorithms, this file transports them across
`E0.orderIsoNONote`.  The resulting operations remain computational on
finite syntax, while their correctness follows from the established bridge.
-/

namespace OrdinalAnalysis
namespace E0

/-- Use the existing canonical zero term as the `Zero` instance. -/
instance instZero : Zero E0 where
  zero := E0.zero

/-- Use the existing canonical one term as the `One` instance. -/
instance instOne : One E0 where
  one := E0.one

/-- Ordinal addition transported from mathlib's `NONote`. -/
def add (a b : E0) : E0 :=
  ofNONote (toNONote a + toNONote b)

instance instAdd : Add E0 where
  add := add

/-- Ordinal subtraction transported from mathlib's `NONote`. -/
def sub (a b : E0) : E0 :=
  ofNONote (toNONote a - toNONote b)

instance instSub : Sub E0 where
  sub := sub

/-- Ordinal multiplication transported from mathlib's `NONote`. -/
def mul (a b : E0) : E0 :=
  ofNONote (toNONote a * toNONote b)

instance instMul : Mul E0 where
  mul := mul

/-- Ordinal exponentiation transported from mathlib's `NONote`. -/
def opow (a b : E0) : E0 :=
  ofNONote (NONote.opow (toNONote a) (toNONote b))

instance instPow : Pow E0 E0 where
  pow := opow

@[simp]
theorem toNONote_add (a b : E0) :
    toNONote (a + b) = toNONote a + toNONote b := by
  change toNONote (ofNONote (toNONote a + toNONote b)) =
    toNONote a + toNONote b
  exact toNONote_ofNONote _

@[simp]
theorem toNONote_sub (a b : E0) :
    toNONote (a - b) = toNONote a - toNONote b := by
  change toNONote (ofNONote (toNONote a - toNONote b)) =
    toNONote a - toNONote b
  exact toNONote_ofNONote _

@[simp]
theorem toNONote_mul (a b : E0) :
    toNONote (a * b) = toNONote a * toNONote b := by
  change toNONote (ofNONote (toNONote a * toNONote b)) =
    toNONote a * toNONote b
  exact toNONote_ofNONote _

@[simp]
theorem toNONote_pow (a b : E0) :
    toNONote (a ^ b) = NONote.opow (toNONote a) (toNONote b) := by
  change toNONote
      (ofNONote (NONote.opow (toNONote a) (toNONote b))) =
    NONote.opow (toNONote a) (toNONote b)
  exact toNONote_ofNONote _

/-- Evaluation commutes with notation-level ordinal addition. -/
@[simp]
theorem eval_add (a b : E0) :
    eval (a + b) = eval a + eval b := by
  calc
    eval (a + b) = NONote.repr (toNONote (a + b)) :=
      (repr_toNONote (a + b)).symm
    _ = NONote.repr (toNONote a + toNONote b) := by
      rw [toNONote_add]
    _ = NONote.repr (toNONote a) + NONote.repr (toNONote b) :=
      NONote.repr_add _ _
    _ = eval a + eval b := by
      rw [repr_toNONote, repr_toNONote]

/-- Evaluation commutes with notation-level ordinal subtraction. -/
@[simp]
theorem eval_sub (a b : E0) :
    eval (a - b) = eval a - eval b := by
  calc
    eval (a - b) = NONote.repr (toNONote (a - b)) :=
      (repr_toNONote (a - b)).symm
    _ = NONote.repr (toNONote a - toNONote b) := by
      rw [toNONote_sub]
    _ = NONote.repr (toNONote a) - NONote.repr (toNONote b) :=
      NONote.repr_sub _ _
    _ = eval a - eval b := by
      rw [repr_toNONote, repr_toNONote]

/-- Evaluation commutes with notation-level ordinal multiplication. -/
@[simp]
theorem eval_mul (a b : E0) :
    eval (a * b) = eval a * eval b := by
  calc
    eval (a * b) = NONote.repr (toNONote (a * b)) :=
      (repr_toNONote (a * b)).symm
    _ = NONote.repr (toNONote a * toNONote b) := by
      rw [toNONote_mul]
    _ = NONote.repr (toNONote a) * NONote.repr (toNONote b) :=
      NONote.repr_mul _ _
    _ = eval a * eval b := by
      rw [repr_toNONote, repr_toNONote]

/-- Evaluation commutes with notation-level ordinal exponentiation. -/
@[simp]
theorem eval_pow (a b : E0) :
    eval (a ^ b) = eval a ^ eval b := by
  calc
    eval (a ^ b) = NONote.repr (toNONote (a ^ b)) :=
      (repr_toNONote (a ^ b)).symm
    _ = NONote.repr (NONote.opow (toNONote a) (toNONote b)) := by
      rw [toNONote_pow]
    _ = NONote.repr (toNONote a) ^ NONote.repr (toNONote b) :=
      NONote.repr_opow _ _
    _ = eval a ^ eval b := by
      rw [repr_toNONote, repr_toNONote]

end E0
end OrdinalAnalysis
