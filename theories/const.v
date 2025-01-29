From PangoLang Require Import ir.
Require Import Coq.Program.Wf.
Require Import FunInd.
Require Import Lia.
Require Import Coq.Program.Tactics.
From Coq Require Import FMaps.

From Equations Require Import Equations.

Import CPS.
Open Scope cps_scope.

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

Definition tr_matches src opt := src.(tr) = opt.(tr).
Definition st_matches src opt := forall f src_bod args,
    Some (args, src_bod) = FnMap.find f src.(fstor) ->
    exists opt_bod,
    Some (args, opt_bod) = FnMap.find f opt.(fstor) /\
        opt_bod = const_fold src_bod.
                            

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

Theorem const_fold_preserve_fvs: forall e, (fun exp =>
    (forall n, NatSet.Equal (fvs_rec (const_fold exp) n) (fvs_rec exp n))) e.
Proof.
    apply well_founded_ind with (R := cexp_rel).
    - apply cexp_rel_wf.
    - intros. destruct x eqn:Hx.
      + destruct op, lhs, rhs; autorewrite with const_fold; simpl; do 2 apply NSProp.union_equal_2;
        try (apply H; unfold cexp_rel; unfold ltof; simpl; auto with arith). 
        * assert (Heq: NatSet.Equal (fvs_rec c (S n)) (fvs_rec (substitute 0 (i64 (Int64.mul n0 n1)) c) (S n))).
           { rewrite subst_fvs_gt. reflexivity. lia. }
          rewrite Heq. apply H. unfold cexp_rel; unfold ltof.
          rewrite <- subst_preserve_depth with (n := O) (v := i64 (Int64.mul n0 n1)).
          auto with arith.
Admitted.

Theorem const_fold_subst_idempotent: forall k v,
    (const_fold (substitute 0 v k)) = 
    (substitute 0 v (const_fold (substitute 0 v k))).
Proof.
    intros. remember (fvs k) as nfvs eqn:Hnfvs.
    remember (substitute 0 v k) as sk eqn:Hsk.
    remember (fvs sk) as nfvs' eqn:Hfvs'.
    assert (H: ~ NatSet.In 0 nfvs').
    { rewrite Hfvs'. apply eq_sym in Hsk. now apply subst_remove_fvs in Hsk. }
    apply subst_invariant.
    remember (fvs (const_fold sk)) as fvsc eqn:Hfvsc.
    apply eq_sym in Hfvsc.
    unfold fvs in Hfvsc.
    rewrite <- Hfvsc. unfold "~". intros.
    apply H. rewrite Hfvs'.
    now apply const_fold_preserve_fvs with (n := 0).
Qed.

Corollary const_fold_app: forall f_params args f_body,
    const_fold (apply_args f_body f_params args) = apply_args (const_fold f_body) f_params args.
Proof.
    intros n. induction n.
    - intros args. destruct args; trivial.
    - intros args. destruct args.
        + now simpl.
        + simpl. intros. rewrite IHn.
Admitted.

Inductive First {A B C} : (A * B * C) -> list (A * B * C) -> Prop :=
    | First_hd : forall x xs, First x (x :: xs)
    | First_tl : forall a1 a2 a3 b1 b2 b3 tl, a1 <> b1 -> 
        First (a1, a2, a3) tl -> First (a1, a2, a3) ((b1, b2, b3) :: tl).

Remark first_implies_in: forall A B C (e: A * B * C) l, First e l -> In e l.
Proof.
    intros. induction H.
    - apply in_eq.
    - apply in_cons. assumption.
Qed.

Lemma first_append_map_fns: forall f args src_bod fns st (fn : cexp -> cexp),
    First (f, args, src_bod) fns -> 
    (FnMap.find f 
        (append_fns (in_map fns (fun e _ => let '(a, b, _) := e in
            (a, b, fn (snd e)))) st) = Some (args, fn src_bod)).
Proof.
    intros. remember (f, args, src_bod) as e. induction H.
    - autorewrite with in_map. destruct x. destruct p. simpl.
        inversion Heqe. apply FMFact.add_eq_o. reflexivity.
    - autorewrite with in_map. simpl. rewrite FMFact.add_neq_o.
        + apply IHFirst. now inversion Heqe.
        + unfold "<>". intros Heq. inversion Heqe as (Heq1).
            assert (a1 = b1) by (rewrite Heq; rewrite Heq1; reflexivity).
            contradiction.
Qed.

Theorem find_append_map: forall k l s ra rb,
    Some (ra, rb) = FnMap.find k (append_fns l s) ->
    (Some (ra, rb) = FnMap.find k s /\ forall ra' rb', ~ In (k, ra', rb') l)
        \/ First (k, ra, rb) l.
Proof.
    intros. induction l.
    - simpl in H. left. split; auto.
    - simpl in H. destruct a. destruct p. destruct (String.eqb k s0) eqn: H'.
        + apply String.eqb_eq in H'. right. rewrite H' in H.
            rewrite FMFact.add_eq_o in H. inversion H. rewrite H'. apply First_hd. 
            reflexivity.
        + apply String.eqb_neq in H'. rewrite FMFact.add_neq_o in H.
            * apply IHl in H. destruct H.
                -- left. destruct H. split; auto. unfold "~". intros.
                    inversion H1.
                    ++ apply H'. now inversion H2. 
                    ++ now apply H0 in H2.
                -- right. apply First_tl; assumption.
            * unfold "<>" in *. intros. destruct H'. auto.
Qed.

Lemma not_in_append: forall f st l,
    (forall a b, ~ In (f, a, b) l) -> FnMap.find f (append_fns l st) = FnMap.find f st.
Proof. 
    intros f st l. induction l.
    - intros. now simpl.
    - intros. simpl. destruct a. destruct p.
        pose proof H as H'. specialize H with (a := n) (b := c).
        unfold "~" in H.
        assert (f <> k).
        { unfold "<>". intros. apply H. rewrite H0. apply in_eq. }
        rewrite FMFact.add_neq_o.
        +  apply IHl. unfold "~". intros a b H''.
            apply in_cons with (a := (k, n, c)) in H''.
            now apply H' in H''.
        + unfold "<>" in *. intros H1. apply eq_sym in H1.
            now apply H0.
Qed.

Lemma in_map_nil: forall A B (l: list A) (f: forall (a: A), In a l -> B), 
    in_map l f = nil <-> l = nil.
Proof.
    intros A B l. split.
    - intros. destruct l.
        + trivial.
        + discriminate.
    - intros. generalize dependent f. rewrite H. intros. now autorewrite with in_map.
Qed.

Lemma in_cons_neq: forall A B C (f s: A) (a c: B) (b d: C) (l: list (A * B * C)),
    f <> s -> In (f, a, b) ((s, c, d) :: l) <-> In (f, a, b) l.
Proof.
    intros. split. 
    - intros. destruct H0.
        + inversion H0. apply eq_sym in H2. contradiction.
        + assumption.
    - intros. now apply in_cons. 
Qed. 

Lemma in_map_nth: forall k (f: cexp -> cexp) n l,
    Some k = nth_error l n -> Some (f k) = nth_error (in_map l (fun e _ => f e)) n.
Proof.
    intros k f n. induction n.
    - intros. destruct l.
        + discriminate.
        + simpl. autorewrite with in_map. simpl in H. now inversion H.
    - intros. destruct l.
        + discriminate.
        + simpl. autorewrite with in_map. simpl in *. now apply IHn.
Qed.


Theorem const_fold_step: forall c s c' s' s_2,
    c @ s --> c' @ s' -> st_matches s s_2 -> tr_matches s s_2 -> exists s'', 
        (const_fold c) @ s_2 --> (const_fold c') @ s'' /\ st_matches s' s'' /\ tr_matches s' s''.
Proof.
    intros. destruct H.
    - eexists ?[s'']. split.
        + autorewrite with const_fold. 
          rewrite const_fold_subst_idempotent at 2. now apply sbop.
        + split; assumption.
    - eexists ?[s'']. split.
        + autorewrite with const_fold. rewrite const_fold_subst_idempotent at 2. now apply suop.
        + split; assumption.
    - autorewrite with const_fold. unfold st_matches in H0. unfold tr_matches in H1.
      pose proof H as H'. apply H0 in H. case H; intros. destruct H2.
      exists s_2. split. 
        + rewrite const_fold_app. rewrite <- H3. apply sapp. assumption.
        + unfold st_matches. unfold tr_matches. split; assumption.
    - autorewrite with const_fold. 
        exists {| tr := tr s_2; fstor := append_fns (in_map fns (fun e _ => 
            let '(a, b, _) := e in (a, b, const_fold (snd e)))) s_2.(fstor) |}.
        split.
        + apply sfix.
        + split.
            * unfold st_matches. simpl. intros f src_bod args H.
                apply find_append_map in H. destruct H.
                -- destruct H. unfold st_matches in H0.
                    pose proof H as H'. apply H0 in H.
                    rewrite not_in_append.
                    ++ auto.
                    ++ induction fns.
                        ** unfold "~". intros. destruct H3; auto.
                        ** simpl in *. autorewrite with in_map in *. destruct a. destruct p.
                            assert (H3: ((forall ra' rb', (s, n, c) <> (f, ra', rb')) /\ 
                                (forall ra' rb', ~ In (f, ra', rb') fns))).
                            { 
                                split; intros; specialize H2 with (ra' := ra') (rb' := rb');
                                tauto. 
                            } 
                            destruct H3.
                            assert (H5: s <> f).
                            {
                              specialize H3 with (ra' := n) (rb' := c).
                              unfold "<>". intros. rewrite H5 in H3. now apply H3.
                            }
                            unfold "~". intros.
                            apply IHfns with (a := a) (b := b) in H4.
                            apply H4. rewrite in_cons_neq in H6; (auto || tauto).
                -- rewrite first_append_map_fns with (args := args) (src_bod := src_bod) by assumption. 
                    exists (const_fold src_bod). split; trivial.
            * unfold tr_matches in *. now simpl.
    - eexists ?[s'']. split.
      + autorewrite with const_fold. apply ssel. now apply in_map_nth.
      + split; assumption.
    - eexists ?[s'']. split.
        + autorewrite with const_fold. apply seff.
        + split.
            * unfold st_matches in *. assumption.
            * unfold tr_matches in *. simpl. now rewrite H1.
Qed.
