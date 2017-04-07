/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/

/--

INCOMPLETE

--/

import init.meta.mathematica .datatypes
open tactic expr


/-constant real : Type
notation `ℝ` := real
axiom rof : linear_ordered_field ℝ
attribute [instance] rof

constant pow : ℝ → ℝ → ℝ
infix `^` := pow-/

constant deriv : (ℝ → ℝ) → (ℝ → ℝ)
constant rpow : ℝ → ℝ → ℝ
infix `^^`:10 := rpow

@[simp]
theorem deriv_add (f g : ℝ → ℝ) :
       deriv (λ x, f x + g x) = λ x, deriv f x + deriv g x :=
sorry

@[simp]
theorem deriv_mul (f g : ℝ → ℝ) :
        deriv (λ x, f x * g x) = λ x, (deriv f x)*(g x) + (deriv g x)*(f x) :=
sorry

--@[simp]
--theorem deriv_pow (r : ℝ) : deriv (λ x, x^r) = λ x, r*(x^(r-1)) :=
--sorry

theorem deriv_const (r : ℝ) : deriv (λ x, r) = λ x, 0 := sorry

theorem deriv_self : deriv (λ x, x) = λ x, 1 := sorry

@[simp]
lemma arith1 : (5 : ℝ) - 1 = 4 := sorry

@[simp]
lemma arith2 : (4 : ℝ) - 1 = 3 := sorry

attribute [simp] zero_mul one_mul

/-meta def norm_num_simp : tactic unit :=
do (lhs, rhs) ← target >>= match_eq,
   trace ("lhs, rhs", lhs, rhs),
   (ln, prf) ← norm_num lhs,
   (rn, prf') ← norm_num rhs,
   trace "got norms",
   transitivity, apply prf, applyc `eq.symm, apply prf'-/

meta def mk_add_expr (t : expr) (e1 e2 : expr) : tactic expr :=
do (sort l) ← infer_type t,
   hap ← to_expr `(has_add %%t) >>= mk_instance,
   return $ app (app (app (app (const `add [l]) t) hap) e1) e2

meta def mk_mul_expr (t : expr) (e1 e2 : expr) : tactic expr :=
do (sort l) ← infer_type t,
   hap ← to_expr `(has_mul %%t) >>= mk_instance,
   return $ app (app (app (app (const `mul [l]) t) hap) e1) e2

meta def find_deriv_add (find_deriv : expr → tactic (expr × expr)) (vn : name) (bi : binder_info) (tp : expr) (bod : expr) : tactic (expr × expr) := do trace ("in find_deriv_add", bod),
 [_, _, lhs, rhs] ← match_app_of bod `add,
 (lam _ _ _ lhsval, prl) ← find_deriv (lam vn bi tp lhs),
 (lam _ _ _ rhsval, prr) ← find_deriv (lam vn bi tp rhs),
 ae ← mk_add_expr tp lhsval rhsval,
 let rv := lam vn bi tp ae,
 tgt ← to_expr `(deriv %%(lam vn bi tp bod) = %%rv),
 prf ← mk_inhabitant_using tgt (do transitivity, applyc `deriv_add, applyc `funext, rw' prl, rw' prr),
 return $ (rv, prf)


meta def find_deriv_mul (find_deriv : expr → tactic (expr × expr)) (vn : name) (bi : binder_info) (tp : expr) (bod : expr) : tactic (expr × expr) := do trace ("in find_deriv_mul", bod),
 [_, _, lhs, rhs] ← match_app_of bod `mul,
 (lam _ _ _ lhsval, prl) ← find_deriv (lam vn bi tp lhs),
 (lam _ _ _ rhsval, prr) ← find_deriv (lam vn bi tp rhs),
 ae1 ← mk_mul_expr tp lhsval rhs,
 ae2 ← mk_mul_expr tp rhsval lhs,
 ae ← mk_add_expr tp ae1 ae2,
 let rv := lam vn bi tp ae,
 tgt ← to_expr `(deriv %%(lam vn bi tp bod) = %%rv),
 prf ← mk_inhabitant_using tgt (do trace "trying", trace_state, transitivity, applyc `deriv_mul, trace_state, applyc `funext,  dsimp,  intros, trace_state, infer_type prl >>= trace, to_expr `(eq.symm %%prl) >>= rw', trace_state, rw' prr, trace_state, reflexivity),
 return $ (rv, prf)

example (h1 : deriv (λ x : ℝ, (4 : ℝ)) = λ x : ℝ, 0) : ∀ x, deriv (λ (x : ℝ), 4) x * x + deriv (λ (x : ℝ), x) x * 4 = 0 * x + 1 * 4 := begin
intro,
rw h1,
dsimp,

end

meta def find_deriv_const (vn : name) (bi : binder_info) (tp : expr) (bod : expr) : tactic (expr × expr) := 
 if bod^.has_var then match bod with
 | var 0 := do trace "is x", prf ← mk_const `deriv_self, res ← to_expr `(λ x : ℝ, (1 : ℝ)), return (res, prf)
 | a :=  trace ("has var", a) >> failed
 end else do trace "is const",
  rv ← to_expr `(λ x : ℝ, (0 : ℝ)),
  tgt ← to_expr `(deriv %%(lam vn bi tp bod) = %%rv),
  prf ← mk_inhabitant_using tgt (applyc `deriv_const),
  return $ (rv, prf)
 

meta def find_deriv_pow (find_deriv : expr → tactic (expr × expr)) : expr → tactic (expr × expr) := sorry

example : (deriv (λ x, 10)) = λ x, 0 := by do
 (rv, prf) ← find_deriv_const `x binder_info.default ```(ℝ) ```(10 : ℝ),
 trace rv, trace prf, apply prf

meta def find_deriv : expr → tactic (expr × expr)
| (lam x bi tp bd) := do--mk_const `real >>= is_def_eq tp >> infer_type bd >>= is_def_eq tp >> do
  (bdr, pr) ← find_deriv_add find_deriv x bi tp bd <|> find_deriv_mul find_deriv x bi tp bd <|>
  find_deriv_const x bi tp bd,
-- find_deriv_pow find_deriv bd,
--  pr' ← tactic.mk_app `funext [lam x bi tp pr],
--  return (lam x bi tp bdr, pr')
  return (bdr, pr)
| _ := failed

variable x : ℝ

example : deriv (λ x, 5 + 4) = λ x, 0 := by do
(rs, prf) ← to_expr `(λ x : ℝ, (5 : ℝ) + 4*x) >>= find_deriv,
trace rs, trace prf, failed

#exit

example : deriv (λ x, x^^5 + x^^4) = (λ x, 5*x^^4 + 4*x^^3) :=
by do
(rs, prf) ← to_expr `((λ x, x^^5 + x^^4)) >>= find_deriv,
trace rs, trace prf, failed
--simp --rw [deriv_add, deriv_pow, deriv_pow, arith1, arith2]

