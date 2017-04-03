
/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/

import .linarith 
open expr tactic rb_map list matrix
set_option trace.app_builder true
set_option trace.check true
set_option pp.implicit true 
def tester7 (x y : ℤ) 
  (h1 : 2*x + 4*y ≤ 4) (h2 : (-1)*x ≤ 1)
  (h3 : (-1)*y ≤ -5) : false := by not_exists_of_linear_hyps h1 h2 h3

theorem tester8 (a b c d e f g : ℤ)
 (h1 : 1*a + 2*b + 3*c + 4*d + 5*e + 6*f + 7*g ≤ 30)
 (h2 : (-1)*a ≤ 4)
 (h3 : (-1)*b + (-2)*d ≤ -4)
 (h4 : (-1)*c + (-2)*f ≤ -5)
 (h5 : (-1)*e ≤ -3)
 (h6 : (-1)*g ≤ -2) : false :=
by not_exists_of_linear_hyps h1 h2 h3 h4 h5 h6 --[`h1, `h2, `h3, `h4, `h5, `h6]
