From PangoLang Require Import ir.
Require Import Coq.Program.Wf.
Require Import FunInd.
Require Import Lia.
Require Import Coq.Program.Tactics.

From Equations Require Import Equations.

Import CPS.

(** [in_map l f] is just like [map f l] except that the function carries a proof
    that its argument is an element of [l]. *)
Equations in_map {A B: Type} (l: list A) (f: forall (e: A), In e l -> B) : list B :=
    | a :: tl, f => (f a _) :: (in_map tl (fun e H => f e _))
    | _, _ => nil.

Lemma in_map_length: forall A B (l: list A) (f: forall (e: A), In e l -> B),
    length (in_map l f) = length l.
Proof.
    intros. induction l.
    - trivial.
    - simpl. autorewrite with in_map. simpl. rewrite IHl. trivial.
Qed.


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
Equations const_fold (exp: cexp) : cexp by wf (depth exp) Nat.lt :=
    | cbop op (i64 lhs) (i64 rhs) k =>
        cbop op (i64 lhs) (i64 rhs) (const_fold (substitute O (i64 (bop_eval op lhs rhs)) k))
    | cbop op lhs rhs k => cbop op lhs rhs (const_fold k)
    | cuop op (i64 v) k => 
        cuop op (i64 v) (const_fold (substitute O (i64 (uop_eval op v)) k))
    | cuop op b k => cuop op b (const_fold k)
    | capp x y => capp x y
    | cfix fns k => cfix (in_map fns (fun e H => 
                                      let '(a, b, _) := e in 
                                        (a, b, const_fold (snd e)))) 
                    (const_fold k)
    | csel c branches => csel c (in_map branches (fun br H => const_fold br))
    | ceff op args k => ceff op args (const_fold k)
    | fin => fin.
Next Obligation.
rewrite <- subst_preserve_depth with (n := O) (v := i64 (bop_eval op lhs rhs)). auto.
Qed.
Next Obligation.
rewrite <- subst_preserve_depth with (n := O) (v := i64 (uop_eval op v)). auto.
Qed.
Next Obligation.
    simpl. rewrite Nlt_succ_le. apply Nat.max_le_iff.
    left. apply list_max_in. 
    change (depth c0) with ((fun '(_, _, b) => depth b) (s0, n0, c0)).
    apply List.in_map. assumption. Qed.
Next Obligation. simpl. auto with arith. Qed.
Next Obligation. simpl. rewrite Nlt_succ_le. apply list_max_in. apply List.in_map.
assumption. 
Defined.


Definition matches s_1 s_2 := s_1.(tr) = s_2.(tr).

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



Theorem const_fuel_lock_single: forall c c' s_1 s_2 s_1' n,
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

Lemma const_lock_single: forall c c' s_1 s_2 s_1',
    matches s_1 s_2 -> small_step c s_1 c' s_1' ->
    (exists c_2' s_2', small_step (const_fold c) s_2 c_2' s_2' /\ matches s_1' s_2').
Proof.
    intros. destruct H0.
    all: eexists; eexists; split; (assumption || autorewrite with const_fold; simpl; auto).
    (* Select *)
    - autorewrite with const_fold. apply ssel. destruct H0. split.
        * now rewrite in_map_length.
        * assumption.
    (* Select case 2 *)
    - assumption.
    (* Effect *)
    - unfold matches. unfold matches in H. now rewrite H.
Qed.

(* I don't think this is right... *)
Inductive lock_matches: cexp -> State -> cexp -> State -> Prop :=
    | lock_matches_intro: forall c_1 s_1 c_2 s_2, 
        matches s_1 s_2 -> 
        c_2 = const_fold c_1 -> 
        lock_matches c_1 s_1 c_2 s_2
    | lock_matches_step: forall c_1 s_1 c_2 s_2 c_1' s_1' c_2' s_2', 
        lock_matches c_1 s_1 c_2 s_2 ->
        small_step c_1 s_1 c_1' s_1' ->
        small_step c_2 s_2 c_2' s_2' ->
        matches s_1' s_2' ->
        lock_matches c_1' s_1' c_2' s_2'.

(* Or this... *)
Theorem const_lock_simulation: forall c_1 s_1 c_1' s_1' c_2 s_2,
    lock_matches c_1 s_1 c_2 s_2 -> small_step c_1 s_1 c_1' s_1' -> 
    (exists c_2' s_2', small_step c_2 s_2 c_2' s_2' /\ lock_matches c_1' s_1' c_2' s_2').
Proof.
    intros. induction H.
    - pose proof H0 as H'. apply const_lock_single with (s_2 := s_2) in H0; auto.
        destruct H0 as (c_2' & s_2' & H0 & H0'). 
        rewrite <- H1 in H0. exists c_2'. exists s_2'. split.
        + apply H0.
        + apply lock_matches_step with (c_1 := c_1) (s_1 := s_1) (c_2 := c_2) (s_2 := s_2); auto.
            apply lock_matches_intro; auto.
    - rename c_1' into c_1''. rename s_1' into s_1''. rename c_1'0 into c_1'. rename s_1'0 into s_1'.
        Admitted.
    (* intros. inversion H.
    - pose proof H0 as H'. apply const_lock_single with (s_2 := s_2) in H0; auto.
        destruct H0 as (c_2' & s_2' & H0 & H0'). 
        rewrite <- H2 in H0. exists c_2'. exists s_2'. split.
        + apply H0.
        + apply lock_matches_step with (c_1 := c_1) (s_1 := s_1) (c_2 := c_2) (s_2 := s_2); auto.
    -  *)
