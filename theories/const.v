From PangoLang Require Import ir.
Require Import Coq.Program.Wf.
Require Import FunInd.
Require Import Lia.

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
        match op with
        | mul => const_fold (substitute O (i64 (Int64.mul lhs rhs)) k)
        | add => const_fold (substitute O (i64 (Int64.add lhs rhs)) k)
        | sub => const_fold (substitute O (i64 (Int64.sub lhs rhs)) k)
        | _ => exp
        end
    | cbop op lhs rhs k => cbop op lhs rhs (const_fold k)
    | cuop op (i64 v) k => 
        match op with
        | not => const_fold (substitute O (i64 (Int64.not v)) k)
        | id => const_fold (substitute O (i64 v) k)
        end
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
rewrite <- subst_preserve_depth with (n := O) (v := i64 (Int64.mul lhs rhs)). auto.
Qed.
Next Obligation.
rewrite <- subst_preserve_depth with (n := O) (v := i64 (Int64.add lhs rhs)). auto.
Qed.
Next Obligation.
rewrite <- subst_preserve_depth with (n := O) (v := i64 (Int64.sub lhs rhs)). auto.
Qed.
Next Obligation. repeat split. all: discriminate. Qed.
Next Obligation. repeat split. all: discriminate. Qed.
Next Obligation. repeat split. all: discriminate. Qed.
Next Obligation. repeat split. all: discriminate. Qed.
Next Obligation. repeat split. all: discriminate. Qed.
Next Obligation. repeat split. all: discriminate. Qed.
Next Obligation. repeat split. all: discriminate. Qed.
Next Obligation. repeat split. all: discriminate. Qed.
Next Obligation. repeat split. all: discriminate. Qed.
Next Obligation. 
rewrite <- subst_preserve_depth with (n := O) (v := i64 (Int64.not v)). auto.
Qed.
Next Obligation.   
rewrite <- subst_preserve_depth with (n := O) (v := i64 v). auto.
Qed.
Next Obligation. simpl. rewrite Nlt_succ_le. apply Nat.max_le_iff.
    left. apply list_max_in. 
    change (depth c) with ((fun '(_, _, b) => depth b) (s, n, c)).
    apply List.in_map. assumption. Qed.
Next Obligation. simpl. auto with arith. Qed.
Next Obligation. simpl. rewrite Nlt_succ_le. apply list_max_in. apply List.in_map.
assumption. 
Defined.
