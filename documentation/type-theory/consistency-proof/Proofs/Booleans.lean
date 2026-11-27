import Proofs.Typing

/-!
# Booleans as propositions

The kernel reads a boolean `b` where a type is expected as the proposition
`b ~ true`, and writes the equality out, so what it elaborates is an
ordinary equality at its prelude's `Bool` (`crates/kernel/src/prelude.rs`).
A derivation of that term is a derivation by Eq-Form, which is this theorem:
in any signature with a type of booleans, a boolean is a proposition. So
`Lean Consistency` covers the rule with no rule of its own.
-/

open Tm

/-- Declaration `d` is a type of booleans, as the kernel's prelude declares
`Bool`: no parameters, in `@Type 1`, and `False` then `True`, neither with
fields. -/
def Decl.IsBool (d : Decl) : Prop :=
  d.params = [] ∧ d.uniform = 0 ∧ d.level = 1 ∧ d.ctors = [⟨[], []⟩, ⟨[], []⟩]

-- Rule [Bool-Reflection]: a boolean `b` where a type is expected is `b ~ true`,
-- Eq-Form at the booleans
theorem Deriv.boolReflect {N : Nat} {sig : Sig} {Γ : List Tm} {b : Tm} {k : Nat} {d : Decl}
    (hk : sig[k]? = some d) (hd : d.IsBool) (hΓ : Deriv N sig (.wf Γ))
    (hb : Deriv N sig (.ty Γ b (glob (.data k)))) :
    Deriv N sig (.ty Γ (eq 1 (glob (.data k)) b (glob (.ctor k 1))) (sort 0)) := by
  obtain ⟨hp, hu, hl, hc⟩ := hd
  have hA : Deriv N sig (.ty Γ (glob (.data k)) (sort 1)) := by
    have h := Deriv.dataForm (as := []) hk (by rw [hp]; exact Deriv.argsNil hΓ)
    simpa [apps, hl] using h
  have hT : Deriv N sig (.ty Γ (glob (.ctor k 1)) (glob (.data k))) := by
    have h := Deriv.ctor (ps := []) (fs := []) (c := 1) (C := ⟨[], []⟩) hk (by rw [hc]; rfl)
      (by rw [hp, hu]; exact Deriv.argsNil hΓ) (by simpa [Ctor.tele, fieldsTele] using Deriv.argsNil hΓ)
    simpa [apps] using h
  exact Deriv.eqForm (by decide) hA hb hT
