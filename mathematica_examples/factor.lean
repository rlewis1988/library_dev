/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/

import init.meta.mathematica .datatypes
open expr tactic nat


local attribute [simp] left_distrib right_distrib

open mmexpr nat

-- this will be unnecessary when the arithmetic simplifier is finished
@[simp] lemma {u} n2a {α : Type u} [comm_ring α] (x : α) : -(x*2) = (-1)*x + (-1)*x := 
begin rw (mul_comm x 2), change -((1+1)*x) = -1*x + -1*x, simp end

/--
factor e nm will use the Mathematica Factor function to factor e,
use Lean's simplifier to prove that the factored result is equal
to e, and add a hypothesis with name nm to the local environment.
-/
meta def factor (e : expr) (nm : option name) : tactic unit :=
do t ← mathematica.run_command_on (λ s, s ++" // LeanForm // Activate // Factor") e,
   ts ← to_expr t,
   pf ← eq_by_simp e ts,
   match nm with
   | some n := note n pf
   | none := do n ← get_unused_name `h none, note n pf
   end

/-
We add an interactive version of factor for use in begin...end blocks.
-/
namespace tactic
namespace interactive
section
open interactive.types interactive

meta def factor (e : parse texpr) (nm : parse using_ident) : tactic unit :=
do e' ← i_to_expr e,
   _root_.factor e' nm
end

end interactive
end tactic

/-
EXAMPLES
-/

-- we prove x^2-2x+1 is nonnegative by factoring and applying sq_nonneg.
#check @sq_nonneg
example (x : ℝ) : x^2-2*x+1 ≥ 0 :=
begin
factor x^2-2*x+1 using q,
rewrite q,
apply sq_nonneg
end

-- we factor a number of polynomials and look at the results in the context.
example (x y a : ℝ) : true :=
begin
factor x^10-1,
factor x^10-y^10,
factor 2*x^3*y - 2*a^2*x*y - 3*a^2*x^2 + 3*a^4,
trace_state,
triv
end
 
