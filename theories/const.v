From PangoLang Require Import ir.
Require Import Coq.Program.Wf.
Require Import FunInd.
Require Import Lia.
Require Import Coq.Program.Tactics.

Import CPS.

(** [in_map l f] is just like [map f l] except that the function carries a proof
    that its argument is an element of [l]. *)
Program Fixpoint in_map {A B: Type} (l: list A) (f: {a: A | In a l} -> B) : list B :=
    match l with 
    | a :: tl => (f a) :: (in_map tl f)
    | _ => nil
    end.
Next Obligation. simpl. left. reflexivity. Qed.
Next Obligation. simpl. right. auto. Qed.

Lemma list_max_in: forall e l, In e l -> e <= list_max l.
Proof.
    intros. induction l.
    - contradiction.
    - simpl. simpl in H. destruct H.
        + rewrite H. apply Nat.le_max_l.
        + destruct IHl. 
            * trivial.
            * apply Nat.le_max_r.
            * lia.
Qed.

Lemma Nlt_succ_le: forall n m, n < S m <-> n <= m.
Proof. lia. Qed.

(** [const_fold exp] is [exp] with operations of the form
    [n_1 op n_2] or [op n] folded with their values substituted into
    their uses. *)
Program Fixpoint const_fold (exp: cexp) {measure (depth exp)} : cexp :=
    match exp with
    | cbop op (i64 lhs) (i64 rhs) k =>
        cbop op (i64 lhs) (i64 rhs) (const_fold (substitute O (i64 (bop_eval op lhs rhs)) k))
    | cbop op lhs rhs k => cbop op lhs rhs (const_fold k)
    | cuop op (i64 v) k => 
        cuop op (i64 v) (const_fold (substitute O (i64 (uop_eval op v)) k))
    | cuop op b k => cuop op b (const_fold k)
    | capp x y => capp x y
    | cfix fns k => cfix (in_map fns (fun (e: {a: string * nat * cexp | In a fns}) => 
                                      let '(a, b, k) := e in 
                                        (a, b, const_fold k))) 
                    (const_fold k)
    | csel c branches => csel c (in_map branches (fun br => const_fold br))
    | ceff op args k => ceff op args (const_fold k)
    | fin => fin
    end.
Next Obligation.
rewrite <- subst_preserve_depth with (n := O) (v := i64 (bop_eval op lhs rhs)). auto.
Qed.
Next Obligation.
rewrite <- subst_preserve_depth with (n := O) (v := i64 (uop_eval op v)). auto.
Qed.
Next Obligation. simpl. rewrite Nlt_succ_le. apply Nat.max_le_iff.
    left. apply list_max_in. 
    change (depth c) with ((fun '(_, _, b) => depth b) (s, n, c)).
    apply List.in_map. assumption. Qed.
Next Obligation. simpl. auto with arith. Qed.
Next Obligation. simpl. rewrite Nlt_succ_le. apply list_max_in. apply List.in_map.
assumption. 
Defined.

Definition matches s_1 s_2 := s_1.(tr) = s_2.(tr).

Ltac psimpl f := unfold f; rewrite fix_sub_eq; simpl; fold f.

Fixpoint const_fold_fuel (exp: cexp) (fuel: nat): cexp :=
    match (fuel, exp) with
    | (S n, cbop op (i64 lhs) (i64 rhs) k) =>
        cbop op (i64 lhs) (i64 rhs) (const_fold_fuel (substitute O (i64 (bop_eval op lhs rhs)) k) n)
    | (S n, cbop op lhs rhs k) => cbop op lhs rhs (const_fold_fuel k n)
    | (S n, cuop op (i64 v) k) => 
        cuop op (i64 v) (const_fold_fuel (substitute O (i64 (uop_eval op v)) k) n)
    | (S n, cuop op b k) => cuop op b (const_fold_fuel k n)
    | (_, capp x y) => capp x y
    | (S n, cfix fns k) => cfix (map (fun (e: string * nat * cexp) => 
                                      let '(a, b, k) := e in 
                                        (a, b, const_fold_fuel k n)) fns) 
                    (const_fold_fuel k n)
    | (S n, csel c branches) => csel c (map (fun br => const_fold_fuel br n) branches)
    | (S n, ceff op args k) => ceff op args (const_fold_fuel k n)
    | (_, fin) => fin
    | (O, x) => x
    end.

Lemma gt_is_succ: forall n m, n > m -> exists n', n = S n'.
Proof.
    intros. inversion H as [ m_1 | m_2 ].
    - now exists m.
    - now exists m_2.
Qed. 



(* TODO: Is this statement actually proving what we want it to prove? *)
Theorem const_lock_sim: forall c c' s_1 s_2 s_1' n,
    matches s_1 s_2 -> small_step c s_1 c' s_1' -> n > depth c ->
    (exists c_2' s_2', small_step (const_fold_fuel c n) s_2 c_2' s_2' /\ matches s_1' s_2').
Proof.
    intros. destruct H0. 
    all: apply gt_is_succ in H1; destruct H1 as (n' & H'); rewrite H'; eexists;
    eexists; split; (assumption || simpl; auto).
    (* Select *)
    - simpl. apply ssel. destruct H0. split.
        * now rewrite map_length.
        * assumption.
    (* Select case 2 *)
    - assumption.
    (* Effect *)
    - unfold matches. unfold matches in H. now rewrite H.
Qed.    

(* Theorem const_fold_eq: forall n c, n > depth c -> const_fold_fuel c n = const_fold c.
Proof.
    induction n.
    - intros. inversion H.
    - intros. simpl. destruct c.
        +    *)
