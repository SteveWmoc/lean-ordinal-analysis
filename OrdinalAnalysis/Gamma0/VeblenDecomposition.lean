import OrdinalAnalysis.Gamma0.SemanticBounds

/-!
# A decreasing Veblen decomposition below Γ₀

Every nonzero ordinal below Γ₀ has a leading Veblen principal term, a positive
natural coefficient, and a remainder smaller than that principal term.

Both inverse-Veblen components and the remainder are strictly smaller than
the original ordinal. These are the termination facts needed to construct a
canonical notation by well-founded recursion in the completeness proof.

This is a semantic decomposition, not an executable normalization algorithm
on the finite raw syntax.
-/

namespace OrdinalAnalysis

open Ordinal

namespace Gamma0Decomposition

/-- Below Γ₀, a positive ordinal cannot be a fixed point of the first Veblen inverse. -/
theorem invVeblen₁_lt_of_pos_lt_gamma_zero {o : Ordinal.{0}}
    (hpos : 0 < o) (hbound : o < Γ₀) :
    Ordinal.invVeblen₁ o < o := by
  apply Ordinal.invVeblen₁_lt_iff.2
  refine ⟨hpos.ne', ?_⟩
  intro hmem
  have hfixed := Ordinal.mem_range_gamma.1 hmem
  exact hbound.not_ge (Ordinal.gamma_zero_le_of_veblen_le hfixed.le)

/--
The inverse index of an additive principal term below Γ₀ is strictly smaller
than that principal term. The inverse argument already has this property in
mathlib, without a Γ₀ hypothesis.
-/
theorem invVeblen₁_lt_opow_of_lt_gamma_zero {x : Ordinal.{0}}
    (hbound : ω ^ x < Γ₀) :
    Ordinal.invVeblen₁ x < ω ^ x := by
  have harg :
      Ordinal.invVeblen₂ x <
        Ordinal.veblen (Ordinal.invVeblen₁ x) (Ordinal.invVeblen₂ x) := by
    rw [Ordinal.veblen_invVeblen₁_invVeblen₂]
    exact Ordinal.invVeblen₂_lt x
  have hindex :
      Ordinal.invVeblen₁ (ω ^ x) = Ordinal.invVeblen₁ x := by
    calc
      Ordinal.invVeblen₁ (ω ^ x) =
          Ordinal.invVeblen₁
            (Ordinal.veblen (Ordinal.invVeblen₁ x) (Ordinal.invVeblen₂ x)) := by
              rw [Ordinal.veblen_invVeblen₁_invVeblen₂]
      _ = Ordinal.invVeblen₁ x := Ordinal.invVeblen₁_veblen harg
  rw [← hindex]
  exact invVeblen₁_lt_of_pos_lt_gamma_zero
    (Ordinal.opow_pos x Ordinal.omega0_pos) hbound

/-- One semantic constructor step, with all recursive inputs certified to decrease. -/
structure Decomposition (o : Ordinal.{0}) where
  index : Ordinal.{0}
  arg : Ordinal.{0}
  /-- One less than the positive coefficient, matching `G0Term.veblen`. -/
  coeff : Nat
  tail : Ordinal.{0}
  index_lt : index < o
  arg_lt : arg < o
  tail_lt : tail < o
  arg_lt_principal : arg < Ordinal.veblen index arg
  tail_lt_principal : tail < Ordinal.veblen index arg
  principal_le : Ordinal.veblen index arg ≤ o
  eval_eq :
    Ordinal.veblen index arg * (coeff.succ : Ordinal.{0}) + tail = o

/-- Every nonzero ordinal below Γ₀ has a decreasing Veblen decomposition. -/
theorem exists_decomposition (o : Ordinal.{0})
    (hne : o ≠ 0) (hbound : o < Γ₀) :
    Nonempty (Decomposition o) := by
  let x := Ordinal.log ω o
  let p := ω ^ x
  have hp : p ≤ o := Ordinal.opow_log_le_self ω hne
  have hpbound : p < Γ₀ := hp.trans_lt hbound
  have hindex : Ordinal.invVeblen₁ x < p :=
    invVeblen₁_lt_opow_of_lt_gamma_zero hpbound
  have harg : Ordinal.invVeblen₂ x < p := Ordinal.invVeblen₂_lt x
  have htail : o % p < p :=
    Ordinal.mod_lt o (Ordinal.opow_ne_zero x Ordinal.omega0_ne_zero)
  have hprincipal :
      Ordinal.veblen (Ordinal.invVeblen₁ x) (Ordinal.invVeblen₂ x) = p :=
    Ordinal.veblen_invVeblen₁_invVeblen₂ x
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.1
    (Ordinal.div_opow_log_lt o Ordinal.one_lt_omega0)
  have hnne : n ≠ 0 := by
    intro hnzero
    have hpos := Ordinal.div_opow_log_pos ω hne
    rw [hn, hnzero, Nat.cast_zero] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnne
  have heq :
      Ordinal.veblen (Ordinal.invVeblen₁ x) (Ordinal.invVeblen₂ x) *
          (k.succ : Ordinal.{0}) + o % p = o := by
    rw [hprincipal, ← hn]
    exact Ordinal.div_add_mod o p
  exact ⟨{
    index := Ordinal.invVeblen₁ x
    arg := Ordinal.invVeblen₂ x
    coeff := k
    tail := o % p
    index_lt := hindex.trans_le hp
    arg_lt := harg.trans_le hp
    tail_lt := htail.trans_le hp
    arg_lt_principal := by rw [hprincipal]; exact harg
    tail_lt_principal := by rw [hprincipal]; exact htail
    principal_le := by rw [hprincipal]; exact hp
    eval_eq := heq
  }⟩

/-- A chosen semantic decomposition for the later well-founded completeness construction. -/
noncomputable def decompose (o : Ordinal.{0})
    (hne : o ≠ 0) (hbound : o < Γ₀) : Decomposition o :=
  Classical.choice (exists_decomposition o hne hbound)

end Gamma0Decomposition
end OrdinalAnalysis
