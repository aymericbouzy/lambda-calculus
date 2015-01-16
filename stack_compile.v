Require Import ZArith.
Require Import List.

Inductive bop: Set := Badd.
Inductive expr: Set :=
| e_cst: Z -> expr
| e_bin: bop -> expr -> expr -> expr.
Fixpoint expr_eval (e: expr): Z :=
match e with
| e_cst i => i
| e_bin Badd e1 e2 => Zplus (expr_eval e1) (expr_eval e2)
end.
Inductive inst: Set :=
| Ipush: Z -> inst
| Iadd: inst.
Fixpoint step (s: list Z) (i: inst): list Z :=
match s, i with
| _, Ipush z => z :: s
| v :: u :: t, Iadd => (Zplus v u) :: t
| _, ladd => nil
end.
Fixpoint fold_left (l: list inst) (s: list Z): list Z :=
match l with
| nil => s
| i :: t => fold_left t (step s i)
end.
Fixpoint exec (l: list inst): list Z :=
match (fold_left l nil) with
| v :: nil => v :: nil
| _ => nil
end.
Fixpoint compile (e: expr): list inst :=
match e with
| e_cst i => (Ipush i) :: nil
| e_bin Badd e1 e2 => (compile e1) ++ (compile e2) ++ (Iadd :: nil)
end.

Lemma partial_exec : forall e: expr, forall l1: list inst, forall l2: list Z, fold_left ((compile e) ++ l1) l2 = fold_left l1 ((expr_eval e) :: l2).
Proof.
intros.
induction e.
simpl.


Lemma eq_eval_exec_compile_offset : forall l: list Z, forall e: expr, (expr_eval e) :: l = (fold_left (compile e) nil) ++ l.
Proof.
intros.
induction e.
simpl.
trivial.
induction b.
simpl.

Theorem eq_eval_exec_compile: forall e: expr, (expr_eval e) :: nil = exec (compile e).
Proof.
