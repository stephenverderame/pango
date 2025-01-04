Require Export Coq.Strings.String.
Open Scope string_scope.
Require Export compcert.lib.Integers.
Require Export ZArith.
Require Export Coq.Lists.List.
Open Scope list_scope.
Open Scope nat_scope.
Import ListNotations.
Require Import Arith.

Module CPS.

Inductive value : Type :=
    | var (s: nat)
    | label (s: string)
    | i64 (n : Int64.int)
    | arg (n: nat).

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
    [body] where the fixpoint has [param] number of arguments.
    
    Parameters are given numbers in right-to-left order so that the
    first argument is assigned [param - 1]. *)
Fixpoint apply_args (body: cexp) (param: nat) (args: list value) : cexp :=
    match (param, args) with
    | (S n, head_a :: tail_a) =>
        apply_args (substitute n head_a body) n tail_a
    | _ => body
    end.

(** The trace of observable effects. *)
Definition trace := list (efop * list value).

(** A mapping from function name to definition. *)
Definition fn_store := string -> nat * cexp.

Record State := { tr: trace; fstor: fn_store; }.

(** [append_fns fns st] appends the function definitions at the given fixpoint
    in [fns] to [st]. *)
Fixpoint append_fns (fns: list (string * nat * cexp)) (st: fn_store) : fn_store :=
    match fns with 
    | (name, args, body) :: tl => append_fns tl 
        (fun key => if eqb key name then (args, body) else st key)
    | nil => st
    end.

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
    | sapp : forall st f args,
        small_step (capp (label f) args) st
                   (let '(params, k) := st.(fstor) f in apply_args k params args) st
    | sfix : forall st fns k,
        small_step (cfix fns k) st k 
            {| tr := st.(tr); fstor := (append_fns fns st.(fstor)) |}
    | ssel : forall st cond branches,
        Int64.lt cond (Int64.repr (Z.of_nat (length branches))) = true /\ 
        Int64.lt cond (Int64.repr 0%Z) = false ->
        small_step (csel (i64 cond) branches) st 
            (nth_default fin branches (Z.abs_nat (Int64.unsigned cond))) st
    | seff : forall st args k,
        small_step (ceff print args k) st k 
            {| tr := ((print, args) :: st.(tr)); fstor := st.(fstor) |}.


Theorem determinism: forall c s c_1 s_1 c_2 s_2,
    small_step c s c_1 s_1 /\ small_step c s c_2 s_2 ->
    c_1 = c_2 /\ s_1 = s_2.
Proof.
    destruct c. all: intros; destruct H; inversion H; 
        try (inversion H0; split; try congruence).
    - assert (HA: label f = label f0) by congruence. inversion HA.
      assert (HB: s_1 = s_2) by congruence. now rewrite HB.
Qed.         


(* Multi step relation (aka Star) *)
Inductive multi_step : cexp -> State -> cexp -> State -> Prop :=
    | refl: forall e s, multi_step e s e s
    | trans: forall e s e' s' e'' s'',
        small_step e s e' s' /\ multi_step e' s' e'' s'' ->
        multi_step e s e'' s''.


Example step_add: small_step 
    (cbop add (i64 (Int64.repr 1%Z)) (i64 (Int64.repr 2%Z)) 
        (ceff print [var O] fin)) {| tr := nil; fstor := (fun _ => (O, fin)) |} 
    (ceff print [i64 (Int64.repr 3%Z)] fin) 
        {| tr := nil; fstor := (fun _ => (O, fin)) |}.
Proof. constructor. left. discriminate. Qed.

#[export]
Hint Constructors small_step : core.

End CPS.


