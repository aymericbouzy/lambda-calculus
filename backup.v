





simpl.
assert ((n = i + p) \/ (n = S i + p) \/ (n <> i  + p /\ n <> S i + p)).
omega.
case H0.
intros.
assert (eq_nat_branch n (p + i) (increase_var u p 0)
  (eq_nat_branch n (p + S i) (increase_var a p 0)
     (de_bruijn_aux n l p (S (S i)))) = increase_var u p 0).
apply eq_branch_real_eq.
omega.
rewrite H2.
rewrite neq_branch_real_neq.
rewrite de_bruijn_aux_terminate.
simpl.
apply eq_branch_real_eq.
trivial.
omega.
omega.
intros.
case H1.
intros.
assert (eq_nat_branch n (p + S i) (increase_var a p 0)
     (de_bruijn_aux n l p (S (S i))) = increase_var a p 0).
rewrite eq_branch_real_eq.
trivial.
omega.
rewrite H3.
assert (eq_nat_branch n (p + i) (increase_var u p 0) (increase_var a p 0) = increase_var a p 0).
rewrite neq_branch_real_neq.
trivial.
omega.
rewrite H4.
rewrite missing_variable_substitution.
trivial.
simpl in H.
apply increase_var_keeps_close.
case H.
intros.
trivial.
intros.
case H2.
intros.
assert (eq_nat_branch n (p + S i) (increase_var a p 0)
     (de_bruijn_aux n l p (S (S i))) = de_bruijn_aux n l p (S (S i))).
rewrite neq_branch_real_neq.
trivial.
omega.
rewrite H5.
assert (eq_nat_branch n (p + i) (increase_var u p 0) (de_bruijn_aux n l p (S (S i))) = de_bruijn_aux n l p (S (S i))).
rewrite neq_branch_real_neq.
trivial.
omega.
rewrite H6.
assert (n < i + p \/ n > i + p + 1).
omega.
case H7.
intro.
rewrite missing_variable_substitution.
trivial.
rewrite de_bruijn_aux_terminate.
simpl.
trivial.
omega.
intro.
rewrite missing_variable_substitution.
trivial.
simpl in IHl.




induction a.
simpl.
induction n0.
rewrite leq_branch_real_leq.
simpl.
simpl in H.
case H.
intros.
omega.
omega.
simpl.
simpl in H.
case H.
intros.
omega.
simpl.




simpl.
apply closed_implication.
rewrite nil_substitution in IHt.
simpl in IHt.
rewrite nil_subsititution
rewrite missing_variable_substitution.
simpl.
assert ((n = i) \/ (n = S i) \/ (n <> i /\ n <> S i)).
omega.
rewrite increase_is_id.



simpl in IHt.

rewrite IHt.
assert (de_bruijn_substitution (de_bruijn_substitution_list t nil (S i)) u i = de_bruijn_substitution_list t nil (S i)).
apply missing_variable_substitution.


destruct (beq_nat n i);
trivial.
simpl.
intros.
rewrite nil_substitution.
rewrite <- IHt.
rewrite nil_substitution.
trivial.
split.
apply closed_implication.
case H.
trivial.
trivial.
intros.
rewrite nil_substitution.
simpl.
rewrite <- IHt1.
rewrite <- IHt2.
rewrite nil_substitution.
rewrite nil_substitution.
trivial.
exact H.
exact H.
intro.
induction t.
intros.
simpl.
assert ((n = i) \/ (n = S i) \/ (n <> i /\ n <> S i)).
omega.
case H0.
intro.
assert (eq_nat_branch n i (increase_var u i 0)
  (eq_nat_branch n (S i) (increase_var a (S i) 0)
     (de_bruijn_aux n l (S (S i)))) = increase_var u i 0).
apply eq_branch_real_eq.
exact H1.
rewrite H2.
assert (eq_nat_branch n (S i) (increase_var a (S i) 0)
     (de_bruijn_aux n l (S (S i))) = (de_bruijn_aux n l (S (S i)))).
apply neq_branch_real_neq.
omega.
rewrite H3.
assert (de_bruijn_aux n l (S (S i)) = var n).
apply de_bruijn_aux_terminate.
omega.
rewrite H4.
simpl.
apply eq_branch_real_eq.
exact H1.
intros.
case H1.
intros.
assert (eq_nat_branch n (S i) (increase_var a (S i) 0)
     (de_bruijn_aux n l (S (S i))) = increase_var a (S i) 0).
apply eq_branch_real_eq.
exact H2.
rewrite H3.
assert (eq_nat_branch n i (increase_var u i 0) (increase_var a (S i) 0) = increase_var a (S i) 0).
apply neq_branch_real_neq.
omega.
rewrite H4.
apply missing_variable_substitution.
assert (increase_var a (S i) 0 = a).
apply increase_is_id.
simpl in H.
induction a.
simpl.
assert (closed i (var n0)).
case H.
intros.
case H6.
intros.
trivial.
simpl in H5.

induction n0.
assert (gt_nat_branch 0 0 (var (0 + S i)) (var 0) = var 0).
apply leq_branch_real_leq.
trivial.
omega.
rewrite H6.
trivial.
assert (gt_nat_branch (S n0) 0 (var (S n0 + S i)) (var (S n0)) = var (S n0 + S i)).
apply gt_branch_real_gt.
omega.
rewrite H6.
simpl.


case H5.
induction n0.
simpl.
apply closed_implication.
omega.
simpl.
omega.
intros.
induction n0.
simpl.
omega.
simpl.
omega.
case H.
intros.
case H6.
intros.
assert (closed (S i) a = closed i (lambda a)).
simpl.
trivial.
simpl.

rewrite H9.
trivial.
simpl.
case H.
intros.
case H6.
intros.
assert ((closed i a1 /\ closed i a2) = closed i (application a1 a2)).
simpl.
trivial.
rewrite H9.
trivial.
intros.
assert (eq_nat_branch n (S i) (increase_var a (S i) 0)
     (de_bruijn_aux n l (S (S i))) = de_bruijn_aux n l (S (S i))).
apply neq_branch_real_neq.
omega.
rewrite H3.
assert (eq_nat_branch n i (increase_var u i 0) (de_bruijn_aux n l (S (S i))) = de_bruijn_aux n l (S (S i))).
apply neq_branch_real_neq.
omega.
rewrite H4.
apply missing_variable_substitution.

assert (eq_nat_branch n i (increase_var u i 0)
  (eq_nat_branch n (S i) (increase_var a (S i) 0)
     (de_bruijn_aux n l (S (S i)))) = de_bruijn_aux n l (S (S i))).
apply neq_branch_real_neq.
