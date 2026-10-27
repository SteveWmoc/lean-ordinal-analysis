import OrdinalAnalysis.Gamma0.OrderEmbedding

/-!
# Examples of the verified Γ₀ order

These examples exercise the standard order interface and its connection to
ordinal evaluation. The concrete decisions reduce to the raw comparator.
-/

namespace OrdinalAnalysis

-- Strict and non-strict comparison, including equality and reverse cases.
example : G0.zero < G0.one := by decide
example : G0.one ≤ G0.omega := by decide
example : G0.epsilonZero ≤ G0.epsilonZero := by decide
example : ¬ G0.epsilonZero ≤ G0.omega := by decide
example : G0.omega ≠ G0.epsilonZero := by decide

-- Standard order laws are now available to downstream proofs.
example (a b c : G0) (hab : a < b) (hbc : b ≤ c) : a < c :=
  lt_of_lt_of_le hab hbc

example (a b : G0) (hab : a ≤ b) (hba : b ≤ a) : a = b :=
  le_antisymm hab hba

example (a b : G0) : a < b ∨ a = b ∨ b < a :=
  lt_trichotomy a b

-- Evaluation preserves and reflects both order relations.
example (a b : G0) :
    G0.evalOrderEmbedding a ≤ G0.evalOrderEmbedding b ↔ a ≤ b := by
  simp

example (a b : G0) (hab : a < b) : G0.eval a < G0.eval b :=
  G0.eval_strictMono hab

example (a b : G0) (hab : G0.eval a ≤ G0.eval b) : a ≤ b :=
  (G0.eval_le_eval_iff a b).1 hab

end OrdinalAnalysis
