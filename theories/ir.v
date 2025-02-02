From Coq Require Export List FMaps String FSets.
Open Scope string_scope.
Require Export compcert.lib.Integers.
Require Export ZArith.
Open Scope list_scope.
Open Scope nat_scope.
Import ListNotations.
Require Import Arith.
Require Import Lia.

From Equations Require Import Equations.

Module CPS.

Inductive value : Type :=
    | var (s: nat)
    | label (s: string)
    | i64 (n : Int64.int).

Inductive bop : Type :=
    | mul
    | add
    | sub
    | div
    | lt
    | lte
    | gt
    | gte
    | and
    | or
    | xor
    | eq.

Inductive uop : Type := | id | not.

Inductive efop : Type := | print.

Module Ident_Decidable <: DecidableType with Definition t := string.
  Definition t := string.
  Definition eq (x y: t) := x = y.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Definition eq_dec := string_dec.
End Ident_Decidable.

Module FnMap := FMapWeakList.Make(Ident_Decidable).
Module FMFact := FMapFacts.WFacts(FnMap).
Module FMProp := FMapFacts.WProperties(FnMap).

(* de Bruijn notation CPS *)
Inductive cexp : Type :=
    | cbop (op: bop) (lhs rhs : value) (k: cexp)
    | cuop (op: uop) (v: value) (k: cexp)
    | capp (target: value) (args: list value)
    (** A fixpoint consits of a list of (function name, num args, body) and a 
        continuation. *)
    | cfix (fns: list (string * nat * cexp)) (k: cexp)
    | csel (cond: value) (branches: list cexp)
    | ceff (op: efop) (args: list value) (k: cexp)
    | fin.

(** An induction principle for cexp for proofs that need to 'drill down'
    into the branches and functions of [cfix] and [csel] instead of just
    inducting on continuations. *)
Section cexp_ind2.

Definition onSnd {A B : Type} (P : B -> Prop) (xy : A * B) : Prop :=
  P (snd xy).

Variables (P: cexp -> Prop)
          (HBOP: forall op lhs rhs k, P k -> P (cbop op lhs rhs k))
          (HUOP: forall op v k, P k -> P (cuop op v k))
          (HAPP: forall target args, P (capp target args))
          (HSEL: forall cond branches, List.Forall P branches -> P (csel cond branches))
          (HFIX: forall fns k, P k -> List.Forall (onSnd P) fns -> P (cfix fns k))
          (HEFF: forall op args k, P k -> P (ceff op args k))
          (HFIN: P fin).

Fixpoint cexp_ind2 exp: P exp.
Proof.
    destruct exp.
    - apply HBOP. specialize (cexp_ind2 exp). assumption.
    - apply HUOP. specialize (cexp_ind2 exp). assumption.
    - apply HAPP.
    - apply HFIX.
        + specialize (cexp_ind2 exp). assumption.
        + induction fns.
            * trivial.
            * apply Forall_cons.
                ** unfold onSnd. destruct a. simpl.
                   specialize (cexp_ind2 c). assumption.
                ** assumption.  
    - apply HSEL. induction branches.
        + trivial.
        + apply Forall_cons. 
            * specialize (cexp_ind2 a). assumption.
            * assumption.
    - apply HEFF. specialize (cexp_ind2 exp). assumption.
    - apply HFIN.
Qed.

End cexp_ind2.

(** `replace_val name new_val val` replaces [name] with `new_val`
    in [val] if [val] is a varialble with the same name as [name]. *)
Definition replace_val (name: nat) (new_val val: value) :=
    match val with
    | var s => if Nat.eqb name s then new_val else val
    | x => x
    end.

Lemma replace_val_id: forall n v, replace_val n v v = v.
Proof. 
    intros. destruct v. all: simpl; try reflexivity.
    destruct (Nat.eqb_spec n s); try reflexivity.
Qed.

Lemma replace_val_idempotent: forall n v val, 
    replace_val n v (replace_val n v val) = replace_val n v val.
Proof.
    intros. destruct val; try now simpl.
    - destruct (Nat.eqb_spec n s).
        + rewrite e. simpl. rewrite Nat.eqb_refl. 
            apply replace_val_id.
        + simpl. apply Nat.eqb_neq in n0. rewrite n0.
            simpl. now rewrite n0.
Qed.

(** [substitute name val exp] substitues [name] for [val] in [exp]. As we use de Bruijn
    notation, [name] is incremented every time we descend pass another bind point in
    the tree. *)
Fixpoint substitute (name: nat) (val: value) (exp: cexp) {struct exp}: cexp :=
    match exp with
    | cbop op lhs rhs k => cbop op (replace_val name val lhs) (replace_val name val rhs)
        (substitute (S name) val k)
    | cuop op v k => cuop op (replace_val name val v) (substitute (S name) val k) 
    | cfix fns k => cfix (map (fun e => let '(fname, args, body) := e in 
                                      (fname, args, (substitute (name + args) val body))) fns) 
                        (substitute name val k)
    | csel cond branches => csel (replace_val name val cond) 
        (map (fun e => substitute name val e) branches)
    | ceff op args k => ceff op (map (fun e => replace_val name val e) args) 
        (substitute (S name) val k)
    | capp target args => capp (replace_val name val target) 
        (map (fun e => replace_val name val e) args)              
    | fin => fin
    end.

Module NatSet := FSetWeakList.Make(Nat).
Module NSFact := FSetFacts.WFacts(NatSet).
Module NSProp := FSetProperties.WProperties(NatSet).
Module NSDecide := FSetDecide.Decide(NatSet).

Axiom functional_extensionality : forall {X Y: Type} {f g : X -> Y},
  (forall (x: X), f x = g x) -> f = g.

Axiom set_eq_extensionality : forall a b, NatSet.Equal a b <-> a = b.

Equations in_fold_left {A B: Type} (l: list A) (f: forall (acc: B) (e: A), In e l -> B) (acc: B) : B :=
    | hd :: tl, f, acc => in_fold_left tl (fun acc e _ => f acc e _) (f acc hd _)
    | _, _, acc => acc.

Theorem fold_left_eq_in_fold_left: forall A B (f: B -> A -> B) (l: list A) (acc: B),
    fold_left f l acc = in_fold_left l (fun acc e _ => f acc e) acc.
Proof.
    intros. generalize dependent acc. induction l.
    - intros. simpl. autorewrite with in_fold_left. reflexivity.
    - intros. simpl. autorewrite with in_fold_left. rewrite IHl. reflexivity.
Qed.

Definition fvs_val (v: value) (depth: nat) : NatSet.t :=
    match v with
    | var n => if Nat.ltb n depth then NatSet.empty else NatSet.singleton (n - depth)
    | _ => NatSet.empty
    end.

Fixpoint fvs_rec (exp: cexp) (depth: nat) : NatSet.t :=
    match exp with
    | cbop _ lhs rhs k => NatSet.union (fvs_val lhs depth) (NatSet.union (fvs_val rhs depth) (fvs_rec k (S depth)))
    | cuop _ v k => NatSet.union (fvs_val v depth) (fvs_rec k (S depth))
    | cfix fns k => 
        let fvs_fns := List.fold_left (fun acc e => 
            let '(_, args, body) := e in NatSet.union acc (fvs_rec body (depth + args))) fns NatSet.empty in
        NatSet.union fvs_fns (fvs_rec k depth)
    | csel cond branches => 
        List.fold_left (fun acc e => NatSet.union acc (fvs_rec e depth)) branches (fvs_val cond depth)
    | ceff _ args k => 
        List.fold_left (fun acc e => NatSet.union acc (fvs_val e depth)) args (fvs_rec k (S depth))
    | capp target args => 
        List.fold_left (fun acc e => NatSet.union acc (fvs_val e depth)) args (fvs_val target depth)
    | fin => NatSet.empty
    end.

Remark replace_val_invariant: forall s v v',
    ~ NatSet.In s (fvs_val v O) -> replace_val s v' v = v.
Proof.
    intros s v. destruct v; try (intros; simpl; reflexivity).
    - intros. simpl in *. rewrite Nat.sub_0_r in H.
      assert (s <> s0). { intros H'. apply H. rewrite H'. now apply NatSet.singleton_2. }
      destruct (Nat.eqb_spec s s0); (contradiction || trivial).
Qed.

Remark no_fvs_var_lt: forall v n, n > v -> fvs_val (var v) n = NatSet.empty.
Proof.
    intros. destruct v; simpl.
    - assert (H': 0 < n) by auto with arith. apply Nat.ltb_lt in H'. now rewrite H'. 
    - assert (H': S v < n) by auto with arith. apply Nat.ltb_lt in H'. now rewrite H'.
Qed.

Corollary replace_val_invariant2: forall s v v',
    NatSet.mem s (fvs_val v O) = false -> replace_val s v' v = v.
Proof.
    intros. apply NSProp.FM.not_mem_iff in H. apply replace_val_invariant. assumption.
Qed.

Lemma in_fvs_equiv: forall k s n,
    ~ NatSet.In s (fvs_rec k (S n)) -> ~ NatSet.In (S s) (fvs_rec k n).
Proof.
    intros k. induction k using cexp_ind2.
    - simpl. intros. simpl in H. unfold "~". intros.
      (* apply NatSet.union_3 in H0. apply NatSet.union_3. apply IHk.
      Search NatSet.In.
      unfold "~" in *. intros. apply H. apply NSFact.union_iff. right. 
      apply NSFact.union_iff. now right.
    - simpl. intros. apply NatSet.union_3. apply IHk.
      unfold "~" in *. intros. apply H. apply NSFact.union_iff. now right.
    - simpl. intros.  *)
Admitted.

Definition fvs k := fvs_rec k 0.

Theorem subst_invariant: forall s v k, ~ NatSet.In s (fvs k) -> k = substitute s v k.
Proof.
    intros. generalize dependent s. generalize dependent v. induction k.
    - intros. simpl in *. apply NSProp.FM.not_mem_iff in H. unfold fvs in H. 
      unfold fvs_rec in H. rewrite NSProp.Dec.F.union_b in H.
      rewrite NSProp.Dec.F.union_b in H. apply orb_false_elim in H.
      destruct H as [H']. apply orb_false_elim in H. destruct H as [H'']. fold fvs_rec in H.
      apply replace_val_invariant2 with (v' := v) in H'.
      apply replace_val_invariant2 with (v' := v) in H''.
      rewrite H'. rewrite H''. f_equal. apply IHk. apply NSProp.FM.not_mem_iff in H.
      apply in_fvs_equiv in H. apply H.
    - intros. simpl. apply NSProp.FM.not_mem_iff in H. unfold fvs in H. 
      unfold fvs_rec in H. rewrite NSProp.Dec.F.union_b in H.
      apply orb_false_elim in H.
      destruct H as [H']. fold fvs_rec in H.
      apply replace_val_invariant2 with (v' := v0) in H'.
      rewrite H'. f_equal. apply IHk. apply NSProp.FM.not_mem_iff in H.
      apply in_fvs_equiv in H. apply H.
    - intros. simpl. f_equal.
      + destruct target; simpl; try reflexivity.
        destruct (Nat.eqb_spec s s0).
        * rewrite e in H. unfold "~" in H. unfold fvs in H.
          simpl in H. rewrite Nat.sub_0_r in H.
          assert (H': NatSet.In s0 (fold_left (fun (acc : NatSet.t) (e : value) => 
            NatSet.union acc (fvs_val e 0)) args (NatSet.singleton s0))).
          { induction args.
            - simpl. now apply NatSet.singleton_2.
            - simpl. simpl in H. 
        (* apply NSFact.union_3. apply IHargs. }
        apply NSProp.FM.not_mem_iff in H. unfold fvs in H. 
        unfold fvs_rec in H. rewrite NSProp.Dec.F.union_b in H.
        apply orb_false_elim in H. destruct H as [H']. fold fvs_rec in H.
        apply replace_val_invariant2 with (v' := v) in H'.
        rewrite H'. f_equal. apply IHk. apply NSProp.FM.not_mem_iff in H.
        apply in_fvs_equiv in H. apply H. *)
Admitted.

Theorem subst_remove_fvs: forall k k' s v, substitute s v k = k' -> ~ NatSet.In s (fvs k').
Proof.
    intros k. induction k using cexp_ind2.
    -intros.
Admitted.

Lemma fvs_val_gt: forall v v' s n, 
    n > s -> NatSet.Equal (fvs_val (replace_val s (i64 v') v) n) (fvs_val v n).
Proof.
    intros. destruct v; try (simpl; easy).
    - simpl. destruct (Nat.eqb_spec s s0).
        + assert (H0: s0 < n) by lia. apply Nat.ltb_lt in H0. rewrite H0. easy.
        + destruct (Nat.ltb_spec s0 n).
            * simpl. apply Nat.ltb_lt in H0. rewrite H0. easy.
            * simpl. assert (H1: ~ s0 < n) by lia. apply Nat.ltb_nlt in H1. now rewrite H1.
Qed.
 
Lemma fold_left_map_fvs: forall A f (g: A -> nat -> NatSet.t) (args: list A) (b: NatSet.t) n',
    NatSet.Equal
    (fold_left (fun acc e => NatSet.union acc (g (f e) n')) args b)
    (fold_left (fun acc e => NatSet.union acc (g e n')) (map f args) b).
Proof.
    intros A f g args. induction args.
    - intros. easy.
    - intros. simpl. apply IHargs.
Qed.

Lemma fold_left_map_fvs_fns: forall A (f: cexp -> nat -> NatSet.t)
    (fns: list (A * nat * cexp)) b n' s v,
    NatSet.Equal
    (fold_left (fun acc '(_, args, body) => NatSet.union acc (f body (n' + args))) 
        (map (fun '(a, args, body) => (a, args, substitute (s + args) (i64 v) body)) fns) b)
    (fold_left (fun acc '(_, args, body) => NatSet.union acc (f (substitute (s + args) (i64 v) body) (n' + args))) fns b).
Proof.
    intros A f fns. induction fns.
    - intros. easy.
    - intros. simpl. destruct a. destruct p. apply IHfns.
Qed.

Lemma eq_fold_left: forall A f g b b' (l: list A),
    NatSet.Equal b b' -> (forall acc acc' e, NatSet.Equal acc acc' -> NatSet.Equal (f acc e) (g acc' e)) ->
    NatSet.Equal (fold_left f l b) (fold_left g l b').
Proof.
    intros A f g b b' l Heq H. generalize dependent b. generalize dependent b'. induction l.
    - simpl. easy.
    - intros. simpl in *. apply IHl with (b := f b a) (b' := g b' a).
        + now apply H.
Qed.

Lemma eq_in_fold_left: forall A (l: list A) f g b b',
    NatSet.Equal b b' -> (forall acc acc' e H, NatSet.Equal acc acc' -> NatSet.Equal (f acc e H) (g acc' e H)) ->
    NatSet.Equal (in_fold_left l f b) (in_fold_left l g b').
Proof.
    intros. generalize dependent b. generalize dependent b'. induction l.
    - simpl. easy.
    - intros. simpl in *. autorewrite with in_fold_left. apply IHl.
      * intros. now apply H0.
      * now apply H0.  
Qed.

Lemma union_equal_3: forall a a' b b',
    NatSet.Equal a a' -> NatSet.Equal b b' -> NatSet.Equal (NatSet.union a b) (NatSet.union a' b').
Proof.
    intros. rewrite H. rewrite H0. easy.
Qed.

Theorem subst_fvs_gt: forall k v s n', 
    n' > s -> NatSet.Equal (fvs_rec (substitute s (i64 v) k) n') (fvs_rec k n').
Proof.
    intros k. induction k using cexp_ind2.
    - intros. simpl. pose proof H as H'. pose proof H as H''.
      apply fvs_val_gt with (v := lhs) (v' := v) in H.
      apply fvs_val_gt with (v := rhs) (v' := v) in H'.
      rewrite H. rewrite H'. rewrite IHk. reflexivity. lia.
    - intros. simpl. pose proof H as H'. apply fvs_val_gt with (v := v) (v' := v0) in H.
      rewrite H. rewrite IHk. reflexivity. lia.
    - intros. simpl. pose proof H as H'.
      rewrite <- fold_left_map_fvs.
      apply set_eq_extensionality.
      f_equal.
      + apply functional_extensionality. intros. apply functional_extensionality.
        intros k. apply set_eq_extensionality.
        apply fvs_val_gt with (v := k) (v' := v) in H. now rewrite H.
      + apply set_eq_extensionality. apply fvs_val_gt with (v := target) (v' := v) in H.
        now rewrite H. 
    - intros. simpl. rewrite <- fold_left_map_fvs.
      do 2 rewrite fold_left_eq_in_fold_left.
      apply eq_in_fold_left.
      + now apply fvs_val_gt.
      + intros acc acc' e Hin Hacc.
        apply union_equal_3.
        * assumption.
        * induction H.
          -- inversion Hin.
          -- inversion Hin as [Hin' | Hin'].
             ++ rewrite <- Hin'. now apply H.
             ++ now apply IHForall.
    - intros. simpl. rewrite fold_left_map_fvs_fns.
      + apply union_equal_3.
        * do 2 rewrite fold_left_eq_in_fold_left. apply eq_in_fold_left; try reflexivity.
          intros acc acc' e Hin Hacc. destruct e. destruct p. apply union_equal_3; try assumption.
          induction H.
          -- inversion Hin.
          -- inversion Hin as [Eqx | Hin'].
             ++ unfold onSnd in H. rewrite Eqx in H. simpl in H. apply H. lia.
             ++ now apply IHForall.   
        * apply IHk. auto with arith.
    - intros. simpl. rewrite <- fold_left_map_fvs.
      apply eq_fold_left.
      + apply IHk. auto with arith.
      + intros. apply union_equal_3; auto. now apply fvs_val_gt.
    - intros. now simpl.
Qed.



(** The depth of a CPS expression tree. *)
Fixpoint depth exp: nat :=
    match exp with
    | cbop _ _ _ k => S (depth k)
    | cuop _ _ k => S (depth k)
    | cfix fns k => S (max (list_max (map (fun e => let '(_, _, b) := e in depth b) fns)) 
                           (depth k))
    | csel _ branches => S (list_max (map (fun e => depth e) branches))
    | ceff _ _ k => S (depth k)
    | fin => O
    | capp _ _ => O
    end.

Lemma list_eq_cons: forall A (h h': A) (tl tl': list A),
     h = h' -> tl = tl' -> h :: tl = h' :: tl'.
Proof. intros. rewrite H. rewrite H0. reflexivity. Qed.

Lemma subst_preserve_depth: forall e v n, depth e = depth (substitute n v e).
Proof.
    intros e. induction e using cexp_ind2. 
    - intros. simpl. apply Nat.succ_inj_wd. apply IHe.
    - intros. simpl. apply Nat.succ_inj_wd. apply IHe.
    - intros. simpl. reflexivity.
    - intros. simpl. apply Nat.succ_inj_wd. 
        assert (H2: forall l l', l = l' -> list_max l = list_max l').
        { intros. rewrite H0. reflexivity. }
        apply H2. induction branches.
        + trivial.
        + simpl. apply Forall_cons_iff in H. destruct H.
          apply list_eq_cons.
            * apply H.
            * apply IHbranches. assumption.
    - intros. simpl. apply Nat.succ_inj_wd. 
        assert ((depth (substitute n v e)) = (depth e)).
        { rewrite IHe with (v := v) (n := n). reflexivity. }
        rewrite H0. 
        assert (forall a b c, a = b -> max a c = max b c). 
        { intros. rewrite H1. reflexivity. }
        apply H1.
        assert (H2: forall l l', l = l' -> list_max l = list_max l').
        { intros. rewrite H2. reflexivity. }
        apply H2. induction fns.
        + trivial. 
        + simpl. apply Forall_cons_iff in H. destruct H.
         apply list_eq_cons.
         * destruct a. destruct p. apply H.
         * apply IHfns. assumption.
    - intros. simpl. apply Nat.succ_inj_wd. apply IHe.
    - intros. simpl. reflexivity.   
Qed.

Lemma subst_idempotent: forall e v n, 
    substitute n v (substitute n v e) = substitute n v e.
Proof.
    intros e. induction e using cexp_ind2.
    - intros. simpl. rewrite IHe. rewrite replace_val_idempotent. 
      now rewrite replace_val_idempotent.
    - intros. simpl. rewrite IHe. now rewrite replace_val_idempotent.
    - intros. simpl. rewrite replace_val_idempotent.
      rewrite map_map.
      rewrite map_ext_Forall with (g := fun x => replace_val n v x).
      + trivial.
      + apply Forall_forall. intros. apply replace_val_idempotent. 
    - intros. simpl. rewrite replace_val_idempotent.
        rewrite map_map.
        rewrite map_ext_Forall with (g := fun x => substitute n v x).
        + trivial.
        + rewrite Forall_forall in H. apply Forall_forall. intros. now apply H.
    - intros. simpl. f_equal.
        + rewrite map_map.
          rewrite Forall_forall in H. unfold onSnd in H.
          apply map_ext_in.
          intros a Hin. remember a as b. destruct b as (c & d). destruct c.
          assert (H': substitute (n + n0) v (substitute (n + n0) v d) = substitute (n + n0) v d).
          * specialize H with (x := a).
            assert (H': snd a = d). { rewrite <- Heqb; now simpl. } 
            rewrite H' in H. apply H with (n := n + n0) (v := v).
            now rewrite <- Heqb.
          * now rewrite H'.
        + apply IHe.
    - intros. simpl. rewrite map_map. rewrite IHe. f_equal.
      rewrite map_ext_Forall with (g := fun x => replace_val n v x).
      + reflexivity.
      + apply Forall_forall. intros. apply replace_val_idempotent.
    - intros. simpl. reflexivity.
Qed.

(** A well founded relation on [cexp] using [depth] *)
Definition cexp_rel := (ltof cexp depth).

Remark cexp_rel_wf: well_founded cexp_rel.
Proof.
    unfold cexp_rel. apply well_founded_ltof.
Qed.

Definition cexp_gt := (gtof cexp depth).

Remark cexp_gt_wf: well_founded cexp_gt.
Proof.
    unfold cexp_gt. apply well_founded_gtof.
Qed.

(** [apply_args body params args] applies [args] to the body of a fixpoint,
    [body] where the fixpoint has [param] number of arguments.
    
    Parameters are given numbers in right-to-left order so that the
    first argument is assigned [param - 1]. *)
Fixpoint apply_args (body: cexp) (param: nat) (args: list value) : cexp :=
    match param, args with
    | S n, head_a :: tail_a =>
        apply_args (substitute n head_a body) n tail_a
    | _, _ => body
    end.

(** The trace of observable effects. *)
Definition trace := list (efop * list value).

(** A mapping from function name to definition. *)
Definition fstore := FnMap.t (nat * cexp).

Record State := { tr: trace; fstor: fstore; }.

(** [append_fns fns st] appends the function definitions at the given fixpoint
    in [fns] to [st]. *)
Fixpoint append_fns (fns: list (string * nat * cexp)) (st: fstore) : fstore :=
    match fns with 
    | (name, args, body) :: tl =>  
        FnMap.add name (args, body) (append_fns tl st)
    | nil => st
    end.

Fixpoint make_map {A B} (l: list (string * A * B)) : FnMap.t (A * B) :=
    match l with
    | nil => FnMap.empty (A * B)
    | (a, b, c) :: tl => FnMap.add a (b, c) (make_map tl)
    end.

Theorem append_in_fns: forall fns st f b,
    FnMap.find f (make_map fns) = Some b ->
    FnMap.find f (append_fns fns st) = Some b.
Proof.
    induction fns.
    - intros. simpl in *. inversion H.
    - intros. simpl. destruct a. destruct p. simpl in H.
      destruct (String.eqb_spec f s) as [ H' | H' ].
      + rewrite H' in *. rewrite FMFact.add_eq_o in *; trivial.
      + rewrite FMFact.add_neq_o in *; auto.
Qed.

Definition bop_eval op lhs rhs :=
    match op with
    | add => (Int64.add lhs rhs)
    | sub => (Int64.sub lhs rhs)
    | mul => (Int64.mul lhs rhs)
    (* In this representation [x / 0] is [0] *)
    | div => (Int64.divs lhs rhs)
    | lte => if (Int64.cmp Cle lhs rhs) then (Int64.repr 1%Z) else (Int64.repr 0%Z)
    | lt => if (Int64.lt lhs rhs) then (Int64.repr 1%Z) else (Int64.repr 0%Z)
    | gte => if (Int64.cmp Cge lhs rhs) then (Int64.repr 1%Z) else (Int64.repr 0%Z)
    | gt => if (Int64.cmp Cgt lhs rhs) then (Int64.repr 1%Z) else (Int64.repr 0%Z)
    | eq => if (Int64.eq lhs rhs) then (Int64.repr 1%Z) else (Int64.repr 0%Z)
    | and => (Int64.and lhs rhs)
    | or => (Int64.or lhs rhs)
    | xor => (Int64.xor lhs rhs)
    end.

Definition uop_eval op val :=
    match op with
    | id => val
    | not => (Int64.not val)
    end.

Inductive small_step : cexp -> State -> cexp -> State -> Prop :=
    | sbop : forall op lhs rhs st k, op <> div \/ (Int64.unsigned rhs) <> 0%Z ->
        small_step (cbop op (i64 lhs) (i64 rhs) k) st (substitute O (i64 (bop_eval op lhs rhs)) k) st
    | suop : forall op val st k,
        small_step (cuop op (i64 val) k) st (substitute O (i64 (uop_eval op val)) k) st
    | sapp : forall st f args f_body f_params,
        Some (f_params, f_body) = FnMap.find f st.(fstor) ->
        small_step (capp (label f) args) st
                   (apply_args f_body f_params args) st
    | sfix : forall st fns k,
        small_step (cfix fns k) st k 
            {| tr := st.(tr); fstor := (append_fns fns st.(fstor)) |}
    | ssel : forall st cond branches k,
        Some k = nth_error branches (Z.abs_nat (Int64.unsigned cond)) ->
        small_step (csel (i64 cond) branches) st k st
    | seff : forall st args k,
        small_step (ceff print args k) st k 
            {| tr := ((print, args) :: st.(tr)); fstor := st.(fstor) |}.


Theorem determinism: forall c s c_1 s_1 c_2 s_2,
    small_step c s c_1 s_1 /\ small_step c s c_2 s_2 ->
    c_1 = c_2 /\ s_1 = s_2.
Proof.
    destruct c. all: intros; destruct H; inversion H; 
        try (inversion H0; split; try congruence).
Qed. 


(* Multi step relation (aka Star) *)
Inductive multi_step : cexp -> State -> cexp -> State -> Prop :=
    | refl: forall e s, multi_step e s e s
    | trans: forall e s e' s' e'' s'',
        small_step e s e' s' /\ multi_step e' s' e'' s'' ->
        multi_step e s e'' s''.

Declare Scope cps_scope.        
Notation "c1 @ s1 --> c2 @ s2" := (small_step c1 s1 c2 s2) 
    (at level 10, s1 at next level, c2 at next level, s2 at next level) : cps_scope.
Notation "c1 @ s1 -->* c2 @ s2" := (multi_step c1 s1 c2 s2) 
    (at level 10, s1 at next level, c2 at next level, s2 at next level) : cps_scope.


Example step_add: small_step 
    (cbop add (i64 (Int64.repr 1%Z)) (i64 (Int64.repr 2%Z)) 
        (ceff print [var O] fin)) {| tr := nil; fstor := FnMap.empty (nat * cexp) |} 
    (ceff print [i64 (Int64.repr 3%Z)] fin) 
        {| tr := nil; fstor := FnMap.empty (nat * cexp) |}.
Proof. constructor. left. discriminate. Qed.

#[export]
Hint Constructors small_step : core.

End CPS.


