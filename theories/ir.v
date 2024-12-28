Require Export Coq.Strings.String.
Open Scope string_scope.
Require Export compcert.lib.Integers.
Require Export ZArith.
Require Export Coq.Lists.List.
Open Scope list_scope.
Open Scope nat_scope.
Import ListNotations.

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

(* de Bruijn notation CPS *)
Inductive cexp : Type :=
    | cbop (op: bop) (lhs rhs : value) (k: cexp)
    | cuop (op: uop) (v: value) (k: cexp)
    | capp (target: string) (args: list value)
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

(** The trace of observable effects. *)
Definition trace := list (efop * list value).

(** A mapping from function name to definition. *)
Definition fn_store := string -> nat * cexp.

(** `replace_val name new_val val` replaces [name] with `new_val`
    in [val] if [val] is a varialble with the same name as [name]. *)
Definition replace_val (name: nat) (new_val val: value) :=
    match val with
    | var s => if Nat.eqb name s then new_val else val
    | x => x
    end.

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
    | capp target args => capp target (map (fun e => replace_val name val e) args)              
    | fin => fin
    end.

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

(** [apply_args body params args] applies [args] to the body of a fixpoint,
    [body] where the fixpoint has [param] number of arguments. *)
Fixpoint apply_args (body: cexp) (param: nat) (args: list value) : cexp :=
    match (param, args) with
    | (S n, head_a :: tail_a) =>
        apply_args (substitute param head_a body) n tail_a
    | (O, head_a :: _) => substitute O head_a body
    | _ => body
    end.

(** [append_map fns st] appends the function definitions at the given fixpoint
    in [fns] to [st]. *)
Fixpoint append_map (fns: list (string * nat * cexp)) (st: fn_store) : fn_store :=
    match fns with 
    | (name, args, body) :: tl => append_map tl (fun key => 
        if eqb key name then (args, body) else st key)
    | nil => st
    end.

Inductive small_step : cexp -> trace -> fn_store -> cexp -> trace -> fn_store -> Prop :=
    | sadd: forall trace st k lhs rhs,
        small_step (cbop add (i64 lhs) (i64 rhs) k) trace st 
                   (substitute O (i64 (Int64.add lhs rhs)) k) trace st
    | smul : forall trace st k lhs rhs,
        small_step (cbop mul (i64 lhs) (i64 rhs) k) trace st
                   (substitute O (i64 (Int64.add lhs rhs)) k) trace st
    | ssub : forall trace st k lhs rhs,
        small_step (cbop sub (i64 lhs) (i64 rhs) k) trace st
                   (substitute O (i64 (Int64.sub lhs rhs)) k) trace st
    | sdiv : forall trace st k lhs rhs, (Int64.unsigned rhs) <> 0%Z ->
        small_step (cbop div (i64 lhs) (i64 rhs) k) trace st
                   (substitute O (i64 (Int64.divs lhs rhs)) k) trace st

    | slt_t : forall trace st k lhs rhs, Int64.lt lhs rhs = true ->
        small_step (cbop lt (i64 lhs) (i64 rhs) k) trace st
                   (substitute O (i64 (Int64.repr 1%Z)) k) trace st
    | slt_f : forall trace st k lhs rhs, Int64.lt lhs rhs = false ->
        small_step (cbop lt (i64 lhs) (i64 rhs) k) trace st
                   (substitute O (i64 (Int64.repr 0%Z)) k) trace st

    | slte_t : forall trace st k lhs rhs, Int64.cmp Cle lhs rhs = true ->
        small_step (cbop lte (i64 lhs) (i64 rhs) k) trace st
                   (substitute O (i64 (Int64.repr 1%Z)) k) trace st
    | slte_f : forall trace st k lhs rhs, Int64.cmp Cle lhs rhs = false ->
        small_step (cbop lte (i64 lhs) (i64 rhs) k) trace st
                   (substitute O (i64 (Int64.repr 0%Z)) k) trace st

    | sgt_t : forall trace st k lhs rhs, Int64.cmp Cgt lhs rhs = true ->
        small_step (cbop gt (i64 lhs) (i64 rhs) k) trace st
                   (substitute O (i64 (Int64.repr 1%Z)) k) trace st
    | sgt_f : forall trace st k lhs rhs, Int64.cmp Cgt lhs rhs = false ->
        small_step (cbop gt (i64 lhs) (i64 rhs) k) trace st
                   (substitute O (i64 (Int64.repr 0%Z)) k) trace st

    | sgte_t : forall trace st k lhs rhs, Int64.cmp Cge lhs rhs = true ->
        small_step (cbop gte (i64 lhs) (i64 rhs) k) trace st
                   (substitute O (i64 (Int64.repr 1%Z)) k) trace st
    | sgte_f : forall trace st k lhs rhs, Int64.cmp Cge lhs rhs = false ->
        small_step (cbop gte (i64 lhs) (i64 rhs) k) trace st
                   (substitute O (i64 (Int64.repr 0%Z)) k) trace st

    | seq_t : forall trace st k lhs rhs, Int64.eq lhs rhs = true ->
        small_step (cbop eq (i64 lhs) (i64 rhs) k) trace st
                   (substitute O (i64 (Int64.repr 1%Z)) k) trace st
    | seq_f : forall trace st k lhs rhs, Int64.eq lhs rhs = false ->
        small_step (cbop eq (i64 lhs) (i64 rhs) k) trace st
                   (substitute O (i64 (Int64.repr 0%Z)) k) trace st

    | sand : forall trace st k lhs rhs,
        small_step (cbop and (i64 lhs) (i64 rhs) k) trace st
                   (substitute O (i64 (Int64.and lhs rhs)) k) trace st
    | sor : forall trace st k lhs rhs,
        small_step (cbop or (i64 lhs) (i64 rhs) k) trace st
                   (substitute O (i64 (Int64.or lhs rhs)) k) trace st
    | sxor : forall trace st k lhs rhs,
        small_step (cbop xor (i64 lhs) (i64 rhs) k) trace st
                   (substitute O (i64 (Int64.xor lhs rhs)) k) trace st
    | snot : forall trace st k v,
        small_step (cuop not (i64 v) k) trace st
                   (substitute O (i64 (Int64.not v)) k) trace st
    | sid : forall trace st k v,
        small_step (cuop id v k) trace st
                   (substitute O v k) trace st

    | sapp : forall trace st f args,
        small_step (capp f args) trace st
                   (let '(params, k) := st f in apply_args k params args) trace st
    | sfix : forall trace st fns k,
        small_step (cfix fns k) trace st k trace (append_map fns st)
    | ssel : forall trace st cond branches,
        Int64.lt cond (Int64.repr (Z.of_nat (length branches))) = true /\ 
        Int64.lt cond (Int64.repr 0%Z) = false ->
        small_step (csel (i64 cond) branches) trace st 
            (nth_default fin branches (Z.abs_nat (Int64.unsigned cond))) trace st
    | seff : forall trace st args k,
        small_step (ceff print args k) trace st k ((print, args) :: trace) st.

Inductive many_step : cexp -> trace -> fn_store -> cexp -> trace -> fn_store -> Prop :=
    | small: forall e t s e' t' s', small_step e t s e' t' s' -> many_step e t s e' t' s'
    | trans: forall e t s e' t' s' e'' t'' s'',
        small_step e t s e' t' s' /\ small_step e' t' s' e'' t'' s'' ->
        many_step e t s e'' t'' s''.


Example step_add: small_step 
    (cbop add (i64 (Int64.repr 1%Z)) (i64 (Int64.repr 2%Z)) 
        (ceff print [var O] fin)) nil (fun _ => (O, fin))
    (ceff print [i64 (Int64.repr 3%Z)] fin) nil (fun _ => (O, fin)).
Proof. constructor. Qed.


