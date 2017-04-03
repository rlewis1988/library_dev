open tactic expr
universe u

variables {α : Type u} {a b : α}
section semirings
variable  [linear_ordered_semiring α]

theorem bit0_ge_bit0 (h : a ≥ b) : bit0 a ≥ bit0 b := add_le_add h h

theorem bit0_gt_bit0 (h : a > b) : bit0 a > bit0 b := 
add_lt_add h h

theorem bit1_gt_bit0 (h : a ≥ b) : bit1 a > bit0 b := 
suffices a + a + 1 > b + b + 0, by rw add_zero at this; apply this,
add_lt_add_of_le_of_lt (bit0_ge_bit0 h) zero_lt_one

theorem bit0_gt_bit1 (h : a ≥ b + 1) : bit0 a > bit1 b := 
begin
unfold bit0 bit1,
apply lt_of_lt_of_le,
rotate 1,
apply add_le_add,
repeat {apply h},
simp,
apply add_lt_add_right,
apply lt_add_of_pos_right,
apply zero_lt_one
end

theorem bit0_gt_bit1' {c : α} (h : a ≥ c) (h2 : b+1=c) : bit0 a > bit1 b :=
begin apply bit0_gt_bit1, rw h2, apply h
end

theorem bit1_gt_bit1  (h : a > b) : bit1 a > bit1 b := 
add_lt_add_right (bit0_gt_bit0 h) _

theorem bit0_gt_zero (h : a > 0) : bit0 a > 0 :=
add_pos h h

theorem bit1_gt_zero (h : a ≥ 0) : bit1 a > 0 :=
add_pos_of_nonneg_of_pos (add_nonneg h h) zero_lt_one

theorem bit0_gt_one (h : a ≥ 1) : bit0 a > 1 :=
begin
unfold bit0,
rw [-zero_add (1 : α)],
apply add_lt_add_of_lt_of_le,
apply lt_of_lt_of_le,
apply zero_lt_one,
repeat {assumption}
end

theorem bit1_gt_one (h : a > 0) : bit1 a > 1 :=
begin
unfold bit1 bit0,
apply lt_add_of_pos_left,
apply add_pos,
repeat {assumption}
end
end semirings

section rings
variable [linear_ordered_ring α]

theorem gt_neg {c : α} (h : a + b = c) (h2 : c > 0) : a > -b := sorry
end rings

meta def mk_conj_app_of_pred (e : expr) (tp : expr) : ℕ → tactic expr
| 0 := failed
| 1 := do n ← to_expr `(⟨0, dec_trivial⟩ : %%tp), head_beta $ app e n
| (k+1) := do lpr ← mk_conj_app_of_pred k, 
              n ← to_expr `(⟨%%(pexpr.mk_prenum_macro (k)), dec_trivial⟩ : %%tp), 
              rv ← head_beta $ app e n, mk_app `and [lpr, rv]
open nat
meta def forall_fin_into_conj : expr → tactic expr
--| ```(∀ i : fin %%n, %%P) := do mval ← eval_expr nat n, 
| (pi nm bi ```(fin %%n) P) := do mval ← eval_expr nat n, mk_conj_app_of_pred (lam nm bi ```(fin %%n) P) ```(fin %%n) mval
| _ := fail "bah"

/-meta def prove_forall_of_conj {P : expr} (conjpr : expr) (mval : ℕ) : tactic expr := do
 gs ← get_goals,
 set_goals [P],
 k ← intro,
-/ 


set_option eqn_compiler.max_steps 20000
meta def mk_gt_prf (mk_ge_prf : expr → expr → tactic expr) : expr → expr → tactic expr 
| (```(@bit0 %%_ %%_ %%t1)) (```(@bit0 %%_ %%_ %%t2)) := 
   do prf ← mk_gt_prf t1 t2,
      tactic.mk_app `bit0_gt_bit0 [prf]
| (```(@bit1 %%_ %%_ %%_ %%t1)) (```(@bit0 %%_ %%_ %%t2)) := 
   do prf ← mk_ge_prf t1 t2,
      tactic.mk_app `bit1_gt_bit0 [prf]
| (```(@bit0 %%_ %%_ %%t1)) (```(@bit1 %%t %%_ %%_ %%t2)) := 
   do (n, eqp) ← to_expr `(%%t2 + 1 : %%t) >>= norm_num, prf ← mk_ge_prf t1 n,
      tactic.mk_app `bit0_gt_bit1' [prf, eqp]
| (```(@bit1 %%_ %%_ %%_ %%t1)) (```(@bit1 %%_ %%_ %%_ %%t2)) := 
   do prf ← mk_gt_prf t1 t2,
      tactic.mk_app `bit1_gt_bit1 [prf]
| (```(@bit0 %%_ %%_ %%t1)) (```(@_root_.zero %%t %%_)) :=
   do prf ← to_expr `(0 : %%t) >>= mk_gt_prf t1,
      tactic.mk_app `bit0_gt_zero [prf]
| (```(@bit0 %%_ %%_ %%t1)) (```(@one %%t %%_)) :=
   do prf ← to_expr `(1 : %%t) >>= mk_ge_prf t1,
      tactic.mk_mapp `bit0_gt_one [none, none, some t1, some prf]
| (```(@bit1 %%_ %%_ %%_ %%t1)) (```(@_root_.zero %%t %%_)) :=
   do prf ← to_expr `(0 : %%t) >>= mk_ge_prf t1 ,
      tactic.mk_app `bit1_gt_zero [prf]
| (```(@bit1 %%_ %%_ %%_ %%t1)) (```(@one %%t %%_)) :=
   do prf ← to_expr `(0 : %%t) >>= mk_gt_prf t1,
      tactic.mk_app `bit1_gt_one [prf]
| (```(@one %%tp %%_)) (```(@_root_.zero %%_ %%_)) := to_expr `(@zero_lt_one %%tp _) 
| (t1) ```(@neg %%tp %%_ %%t2) :=
  do (n, eqp) ← to_expr `(%%t1 + %%t2) >>= norm_num, prf ← to_expr `(0 : %%tp) >>= mk_gt_prf n,
      tactic.mk_app `gt_neg [eqp, prf]
| a b := tactic.fail "mk_gt_prf failed"


meta def mk_ge_prf : expr → expr → tactic expr := λ e1 e2,
to_expr `((le_refl _ : %%e1 ≥ %%e2)) <|> do
  gtprf ← mk_gt_prf mk_ge_prf e1 e2,
  mk_app `le_of_lt [gtprf]

-- assumes ≥ or > and already normalized
meta def gen_comp_val_prf : expr → tactic expr
| ```(@le %%_ %%_ %%lhs %%rhs) := to_expr `(%%rhs ≥ %%lhs) >>= gen_comp_val_prf
| ```(@_root_.lt %%_ %%_ %%lhs %%rhs) := to_expr `(%%rhs > %%lhs) >>= gen_comp_val_prf
| ```(@ge %%_ %%_ %%lhs %%rhs) := mk_ge_prf lhs rhs
| ```(@gt %%_ %%_ %%lhs %%rhs) := mk_gt_prf mk_ge_prf lhs rhs
| _ := tactic.fail "comp_val' didn't match"

meta def is_num : expr → bool
| ```(@bit0 %%_ %%_ %%t) := is_num t
| ```(@bit1 %%_ %%_ %%_ %%t) := is_num t
| ```(@_root_.zero %%_ %%_) := tt
| ```(@one %%_ %%_) := tt
| _ := ff

meta def rw' := rewrite_core transparency.reducible ff ff occurrences.all ff

meta def gen_comp_val : tactic unit := do
t ← target,
--trace t,
[_, _, lhs, rhs] ← return $ get_app_args t,
if is_num lhs then
  if is_num rhs then gen_comp_val_prf t >>= apply
  else do (rhs', prf) ← norm_num rhs, rw' prf, target >>= gen_comp_val_prf >>= apply
else 
  do (lhs', prfl) ← norm_num lhs, rw' prfl,
  if is_num rhs then do t ← target, t ← gen_comp_val_prf t, apply t
  else do (rhs', prf) ← norm_num rhs, rw' prf, t ← target >>= gen_comp_val_prf, apply t

meta def make_expr_into_num : expr → tactic expr := λ e, do
 --trace "BLOCK 3", trace e,
 t ← infer_type e,
 (do onet ← to_expr `(1 : %%t), unify e onet, return onet) <|>
 (do zerot ← to_expr `(0 : %%t), unify e zerot, return zerot) <|>
 (do m ← mk_meta_var t, b0m ← to_expr `(bit0 %%m), unify e b0m, return b0m) <|>
 (do m ← mk_meta_var t, b1m ← to_expr `(bit1 %%m), unify e b1m, return b1m) <|>
 (do m ← mk_meta_var t, negm ← to_expr `(- %%m), unify e negm, rv ← make_expr_into_num m, to_expr `(- %%rv))

meta def make_expr_into_mul : expr → tactic expr := λ e, do
 t ← infer_type e,
 m1 ← mk_meta_var t, m2 ← mk_meta_var t,
 mk_app `mul [m1, m2] >>= unify e,
 lhs ← make_expr_into_num m1, rhs ← make_expr_into_num m2,
 mk_app `mul [lhs, rhs]

meta def make_expr_into_sum : expr → tactic expr := λ e, (do
 t ← infer_type e,
 m1 ← mk_meta_var t, m2 ← mk_meta_var t,
 mk_app `add [m1, m2] >>= unify e,
-- trace m1, trace m2, get_assignment m1 >>= trace, get_assignment m2 >>= trace,
 lhs ← make_expr_into_sum m1, rhs ← make_expr_into_sum m2,
 mk_app `add [lhs, rhs])
 <|> 
 (make_expr_into_mul e)


 #exit

--set_option trace.app_builder true
--set_option pp.all true
--set_option pp.numerals false
--set_option pp.implicit true

example : (1 : α) > 0 := by gen_comp_val 
example : (2 : α) > 0 := by gen_comp_val 
example : (3 : α) > 0 := by gen_comp_val
example : (4 : α) > 0 := by gen_comp_val
example : (2 : α) > 1 := by gen_comp_val
example : (3 : α) > 1 := by gen_comp_val
example : (4 : α) > 1 := by gen_comp_val
example : (3 : α) > 2 := by gen_comp_val
example : (4 : α) > 2 := by gen_comp_val
example : (4 : α) > 3 := by gen_comp_val
example : (5 : α) > 3 := by gen_comp_val
example : (5 : α) > 4 := by gen_comp_val
example : (5 : α) > 1 := by gen_comp_val
example : (6 : α) > 3 := by gen_comp_val
example : (6 : α) > 5 := by gen_comp_val
example : (7 : α) > 4 := by gen_comp_val
example : (7 : α) > 3 := by gen_comp_val
example : (4503 : α) > 7 := by gen_comp_val
example : (45034234 : α) + 44 > 23213 := by gen_comp_val
example : (45030000 : α) > 4503000+44444 := by gen_comp_val
example : (45030440 * 3 : α) > 4503000+44444 := by gen_comp_val
