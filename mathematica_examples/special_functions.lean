/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/
import init.meta.mathematica .datatypes
open expr tactic

/- 
First we axiomatize what a Bessel function is, 
since they are not defined in the Lean library yet.
Note that the defining property is not actually relevant
for this example.
-/
constant deriv : (ℝ → ℝ) → (ℝ → ℝ)

constant BesselJ (n : ℝ) (z : ℝ) : ℝ

axiom BesselJ_def (n : ℝ) (z : ℝ) : 
z*z*(deriv (deriv (BesselJ n)) z) + z*(deriv (BesselJ n) z) + (z*z-n*n)*(BesselJ n z) = 0


section
open mathematica tactic.mathematica

/-
We add translation rules to interpret Mathematica Bessel
functions properly in Lean.
-/

@[sym_to_pexpr]
meta def BesselJ_trans : sym_trans_pexpr_rule :=
⟨"BesselJ", `(BesselJ)⟩

@[sym_to_expr]
meta def pi_trans : sym_trans_expr_rule :=
⟨"Pi", ```(_root_.pi)⟩

@[sym_to_pexpr]
meta def sin_trans : sym_trans_pexpr_rule :=
⟨"Sin", `(sin)⟩

/-
The file "bessel.m" contains a rule to translate Lean Bessel
functions properly in Mathematica.
The command "load_file" makes this declaration globally accessible
for the remainder of the Mathematica session.
-/
run_cmd load_file "bessel.m"

end


/--
make_bessel_fn_eq takes an expression, presumed to be a Bessel function,
and calls the Mathematica FullSimplify function to reduce it.
It then adds an axiom to the environment stating that the input is equal
to this output, and returns the output along with a proof.
-/
meta def make_bessel_fn_eq (e : expr) : tactic (expr × expr) := 
do pe ← mathematica.run_command_on (λ t, t ++ "// LeanForm // Activate // FullSimplify") e,
   val ← to_expr `(%%pe : ℝ),
   tp ← to_expr `(%%e = %%val),
   nm ← new_aux_decl_name,
   let nm' := `mathematica_axiom ++ nm,
   l ← local_context,
   l' ← mfilter (kdepends_on tp) l,
   gls ← get_goals,
   m ← mk_meta_var tp,
   set_goals [m],
   generalizes l',
   tp' ← target,
   set_goals gls,
   let dcl := declaration.ax nm' [] tp',
   add_decl dcl,
   prf ← mk_const nm',
   return (val, prf)

/--
approx e q assumes that q is a numeral expression. It translates e,
numerically approximates the result with a tolerance of q, adds an 
axiom that e is within q of the approximation,
and returns the approximation along with a proof of this bound.
-/
meta def approx (e q : expr) : tactic (expr × expr) :=
do pe ← mathematica.run_command_on_2 
     (λ e q, "Rationalize[" ++ e ++ " // LeanForm // Activate // N, " ++ q ++ "// LeanForm // Activate]") 
     e q,
   val ← to_expr `(%%pe : ℝ),
   (lb, _) ← to_expr `(%%val - %%q) >>= norm_num,
   (ub, _) ← to_expr `(%%val + %%q) >>= norm_num,
   tgt ← to_expr `(%%lb < %%e ∧ %%e < %%ub),
   nm ← new_aux_decl_name,
   let nm' := `approx_axiom ++ nm,
   let dcl := declaration.ax nm' [] tgt,
   add_decl dcl,
   prf ← mk_const nm',
   return (val, prf)

/-
We add an interactive version of approx so that we can use it in
begin...end blocks.
-/
namespace tactic
namespace interactive
section
open lean lean.parser interactive.types interactive
meta def approx (e : parse qexpr) (q : parse qexpr) : itactic := 
do e' ← i_to_expr e,
   q' ← i_to_expr q,
   (_, prf) ← _root_.approx e' q',
   n ← get_unused_name `approx none,
   tactic.note n prf
end
end interactive
end tactic





/-
The examples begin here.
-/

variable x : ℝ

-- we use def instead of theorem so that the axiom remains in the environment.
def f1 : x*BesselJ 2 x + x*BesselJ 0 x = 2*BesselJ 1 x := by
do (t, _) ← target >>= match_eq,
   (_, prf) ← make_bessel_fn_eq t,
   apply prf

#check mathematica_axiom.f1._aux_1
#print axioms f1


-- while proving this theorem, we add an axiom approximating the value of this Bessel function.
def apr : true :=
begin
 approx (100*BesselJ 2 (13/25)) (0.00001 : ℝ),
 trace_state,
triv
end

#print axioms 
