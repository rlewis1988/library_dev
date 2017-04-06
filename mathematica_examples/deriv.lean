
/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/

import init.meta.mathematica
open tactic expr

set_option class.instance_max_depth 64

constant real : Type
notation `ℝ` := real
axiom rof : linear_ordered_field ℝ
attribute [instance] rof
constant deriv : (ℝ → ℝ) → (ℝ → ℝ)
constant pow : ℝ → ℝ → ℝ
infix `^` := pow

@[simp]
theorem deriv_add (f g : ℝ → ℝ) :
       deriv (λ x, f x + g x) = λ x, deriv f x + deriv g x :=
sorry

@[simp]
theorem deriv_mul (f g : ℝ → ℝ) :
        deriv (λ x, f x * g x) = λ x, (deriv f x)*(g x) + (deriv g x)*(f x) :=
sorry

@[simp]
theorem deriv_pow (r : ℝ) : deriv (λ x, x^r) = λ x, r*(x^(r-1)) :=
sorry

@[simp]
lemma arith1 : (5 : ℝ) - 1 = 4 := sorry

@[simp]
lemma arith2 : (4 : ℝ) - 1 = 3 := sorry

check expr.lam

meta def find_deriv_add (find_deriv : expr → tactic (expr × expr)) (e : expr) : tactic (expr × expr) := do
 [_, _, lhs, rhs] ← match_app_of e `add,
 (lhsval, prl) ← find_deriv lhs,
 (rhsval, prr) ← find_deriv rhs,
 
meta def find_deriv_mul (find_deriv : expr → tactic (expr × expr)) : expr → tactic (expr × expr) := sorry
meta def find_deriv_pow (find_deriv : expr → tactic (expr × expr)) : expr → tactic (expr × expr) := sorry

meta def find_deriv : expr → tactic (expr × expr)
| (lam x bi tp bd) := mk_const `real >>= is_def_eq tp >> infer_type bd >>= is_def_eq tp >> do
  (bdr, pr) ← find_deriv_add find_deriv bd <|> find_deriv_mul find_deriv bd <|> find_deriv_pow find_deriv bd,
  pr' ← tactic.mk_app `funext [lam x bi tp pr],
  return (lam x bi tp bdr, pr')
| _ := failed


example : deriv (λ x, x^5 + x^4) = (λ x, 5*x^4 + 4*x^3) :=
begin
simp --rw [deriv_add, deriv_pow, deriv_pow, arith1, arith2]
end
