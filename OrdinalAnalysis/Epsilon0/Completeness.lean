import OrdinalAnalysis.Epsilon0.Operations
import Mathlib.SetTheory.Ordinal.CantorNormalForm
import Mathlib.SetTheory.Ordinal.Veblen

/-!
# Exact semantic range below ε₀

This file closes the v0.1 ε₀ development by proving that canonical `E0`
notations represent exactly the ordinals below `ε₀`.

The completeness proof deliberately reuses mathlib at two levels:

* `Ordinal.CNF` supplies the finite Cantor-normal-form decomposition of an
  arbitrary ordinal;
* `NONote` arithmetic rebuilds those finite CNF sums while preserving
  normality automatically.

The only recursive step is on finite towers of `ω): an exponent occurring in
the CNF of an ordinal below `ω ^ β` is itself below `β`.
-/

namespace OrdinalAnalysis
namespace E0

open Ordinal

/-- The finite tower `0, 1, ω, ω^ω, ...` used in the characterization of `ε₀`. -/
private noncomputable def omegaTower : Nat → Ordinal
  | 0 => 0
  | n + 1 => ω ^ omegaTower n

@[simp]
private theorem omegaTower_zero : omegaTower 0 = 0 :=
  rfl

@[simp]
private theorem omegaTower_succ (n : Nat) :
    omegaTower (n + 1) = ω ^ omegaTower n :=
  rfl

/-- Our recursive tower is the iterate used by mathlib's `lt_epsilon_zero` theorem. -/
private theorem omegaTower_eq_iterate (n : Nat) :
    omegaTower n = (fun a : Ordinal => ω ^ a)^[n] 0 := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [omegaTower_succ, Function.iterate_succ_apply']
      exact congrArg (fun a : Ordinal => ω ^ a) ih

/-- A canonical notation for `ω`, used when rebuilding an arbitrary CNF. -/
private def omegaNote : NONote :=
  ⟨ONote.omega, by
    unfold ONote.omega
    infer_instance⟩

@[simp]
private theorem repr_omegaNote :
    NONote.repr omegaNote = ω := by
  simp [omegaNote, NONote.repr, ONote.omega]

/--
Rebuild a finite ordinal CNF as a canonical mathlib notation, assuming all
exponents already have canonical representatives below a fixed bound.
-/
private theorem exists_nonote_repr_foldr
    {bound : Ordinal}
    (hrep : ∀ β, β < bound → ∃ e : NONote, NONote.repr e = β) :
    ∀ l : List (Ordinal × Ordinal),
      (∀ p ∈ l, p.1 < bound) →
      (∀ p ∈ l, p.2 < ω) →
      ∃ o : NONote,
        NONote.repr o =
          l.foldr (fun p r => ω ^ p.1 * p.2 + r) 0 := by
  intro l
  induction l with
  | nil =>
      intro _ _
      refine ⟨0, ?_⟩
      change ONote.repr 0 = 0
      rfl
  | cons p l ih =>
      intro hexp hcoeff
      obtain ⟨e, he⟩ := hrep p.1 (hexp p (by simp))
      obtain ⟨n, hn⟩ := lt_omega0.1 (hcoeff p (by simp))
      obtain ⟨tail, htail⟩ :=
        ih
          (fun q hq => hexp q (by simp [hq]))
          (fun q hq => hcoeff q (by simp [hq]))
      refine ⟨NONote.opow omegaNote e * NONote.ofNat n + tail, ?_⟩
      simp only [List.foldr_cons]
      rw [NONote.repr_add, NONote.repr_mul, NONote.repr_opow,
        repr_omegaNote, he, htail, hn]
      change _ * ONote.repr (ONote.ofNat n) + _ = _
      rw [ONote.repr_ofNat]

/--
Every ordinal below the `n`th finite `ω)-tower has a canonical
`NONote` representative.
-/
private theorem exists_nonote_repr_below_omegaTower (n : Nat) :
    ∀ α : Ordinal, α < omegaTower n → ∃ o : NONote, NONote.repr o = α := by
  induction n with
  | zero =>
      intro α hα
      exact
        (not_lt_of_ge (bot_le : (0 : Ordinal) ≤ α)
          (by simpa using hα)).elim
  | succ n ih =>
      intro α hα
      have hα' : α < ω ^ omegaTower n := by
        simpa using hα
      by_cases hzero : α = 0
      · subst α
        refine ⟨0, ?_⟩
        change ONote.repr 0 = 0
        rfl
      · have hlog : log ω α < omegaTower n :=
          (lt_opow_iff_log_lt one_lt_omega0 hzero).1 hα'
        have hexp :
            ∀ p ∈ CNF ω α, p.1 < omegaTower n := by
          intro p hp
          exact (CNF.fst_le_log hp).trans_lt hlog
        have hcoeff :
            ∀ p ∈ CNF ω α, p.2 < ω := by
          intro p hp
          exact CNF.snd_lt one_lt_omega0 hp
        obtain ⟨o, ho⟩ :=
          exists_nonote_repr_foldr ih (CNF ω α) hexp hcoeff
        refine ⟨o, ho.trans ?_⟩
        exact CNF.foldr ω α

/--
Every normal finite ε₀ term lies below some finite `ω)-tower.
-/
private theorem exists_eval_lt_omegaTower
    (t : E0Term) (h : t.IsNormal) :
    ∃ n : Nat, E0Term.eval t < omegaTower n := by
  revert h
  induction t with
  | zero =>
      intro _
      refine ⟨1, ?_⟩
      simp [omegaTower, E0Term.eval]
  | cnf exp coeff tail ihExp ihTail =>
      intro h
      obtain ⟨n, hn⟩ := ihExp h.exp
      have htail :
          E0Term.eval tail < ω ^ E0Term.eval exp :=
        E0Term.eval_tail_lt_leadingPower_of_normal exp coeff tail h
      have hnode :
          E0Term.eval (.cnf exp coeff tail) <
            ω ^ (E0Term.eval exp + 1) :=
        E0Term.eval_cnf_lt_nextPower_of_tail_lt coeff htail
      have hsucc :
          E0Term.eval exp + 1 ≤ omegaTower n :=
        hn.succ_le
      have hopow :
          ω ^ (E0Term.eval exp + 1) ≤ ω ^ omegaTower n :=
        opow_le_opow_right omega0_pos hsucc
      refine ⟨n + 1, ?_⟩
      simpa using hnode.trans_le hopow

/-- Every canonical `E0` notation denotes an ordinal strictly below `ε₀`. -/
theorem eval_lt_epsilon_zero (a : E0) :
    eval a < ε₀ := by
  obtain ⟨n, hn⟩ := exists_eval_lt_omegaTower a.1 a.2
  have htower : omegaTower n < ε₀ := by
    rw [omegaTower_eq_iterate]
    exact iterate_omega0_opow_lt_epsilon_zero n
  exact hn.trans htower

/-- Every ordinal strictly below `ε₀` is represented by a canonical `E0` notation. -/
theorem exists_eval_eq_of_lt_epsilon_zero
    {α : Ordinal} (hα : α < ε₀) :
    ∃ a : E0, eval a = α := by
  obtain ⟨n, hn⟩ := lt_epsilon_zero.1 hα
  have htower : α < omegaTower n := by
    rw [omegaTower_eq_iterate]
    exact hn
  obtain ⟨o, ho⟩ :=
    exists_nonote_repr_below_omegaTower n α htower
  refine ⟨ofNONote o, ?_⟩
  rw [eval_ofNONote, ho]

/-- Membership in the semantic range is exactly the condition of lying below `ε₀`. -/
theorem mem_range_eval_iff {α : Ordinal} :
    α ∈ Set.range eval ↔ α < ε₀ := by
  constructor
  · rintro ⟨a, rfl⟩
    exact eval_lt_epsilon_zero a
  · intro hα
    exact exists_eval_eq_of_lt_epsilon_zero hα

/-- The semantic range of canonical ε₀ notation is exactly the initial segment below `ε₀`. -/
theorem range_eval_eq_Iio_epsilon_zero :
    Set.range eval = Set.Iio ε₀ := by
  ext α
  simpa only [Set.mem_range, Set.mem_Iio] using
    (mem_range_eval_iff (α := α))

end E0
end OrdinalAnalysis
