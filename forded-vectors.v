Require Import PeanoNat.

Definition eq_nat (m n : nat) : Type :=
  match Nat.eqb m n with
  | true => unit
  | false => Empty_set
  end.

Inductive EqNat (m n : nat) : Type :=
  refl_nat: eq_nat m n -> EqNat m n.

Theorem false_O_S : forall n, EqNat 0 (S n) -> Empty_set.
Proof.
  intros.
  destruct X.
  unfold eq_nat in e.
  destruct e.
Defined.

Print false_O_S.

Theorem inj_eq_nat : forall (m n : nat), EqNat m n -> EqNat (S m) (S n).
Proof.
  intros.
  refine (refl_nat _ _ _).
  unfold eq_nat.
  simpl.
  destruct X.
  unfold eq_nat in e.
  exact e.
Defined.

Print inj_eq_nat.

Definition inj_eq_nat' (m n: nat ) (H: EqNat m n) : EqNat (S m) (S n) :=
  refl_nat (S m) (S n)
    (match H with
     | refl_nat _ _ e => (fun e0 : eq_nat m n => e0) e
     end).

Theorem proj_eq_nat : forall (m n : nat), EqNat (S m) (S n) -> EqNat m n.
Proof.
  intros.
  constructor.
  unfold eq_nat.
  destruct X.
  unfold eq_nat in e.
  simpl in e.
  exact e.
Defined.

Print proj_eq_nat.

Theorem sym_eq_nat: forall (m n : nat), EqNat m n -> EqNat n m.
Proof.
  intro m.
  induction m; intros.
  - destruct n.
    + exact X.
    + destruct (false_O_S n X).
  - destruct n.
    + destruct X.
      unfold eq_nat in e.
      destruct e.
    + pose proof (proj_eq_nat m n X) as H0.
      apply IHm in H0.
      apply inj_eq_nat.
      exact H0.
Defined.

Print sym_eq_nat.

Theorem trans_eq_nat: forall m n o, EqNat m n -> EqNat n o -> EqNat m o.
Proof.
  intro m.
  induction m; destruct n; intros.
  + exact X0.
  + destruct (false_O_S n X).
  + destruct (false_O_S m (sym_eq_nat (S m) 0 X)).
  + destruct o.
    - destruct (false_O_S n (sym_eq_nat (S n) 0 X0)).
    - pose proof (proj_eq_nat m n X) as Heq_m_n.
      pose proof (proj_eq_nat n o X0) as Heq_n_o.
      pose proof (IHm n o Heq_m_n Heq_n_o) as Heq_m_o.
      apply inj_eq_nat.
      exact Heq_m_o.
Defined.

Print trans_eq_nat.

Theorem refl_eq_nat : forall n, EqNat n n.
Proof.
  intro.
  induction n.
  - apply refl_nat.
    unfold eq_nat.
    exact tt.
  - apply inj_eq_nat.
    exact IHn.
Defined.

Print refl_eq_nat.

Theorem subst_eq_nat: forall m n (P: forall (n : nat), Type), EqNat m n -> P m -> P n.
Proof.
  induction m; induction n; intros.
  - exact X0.
  - destruct (false_O_S n X).
  - destruct (false_O_S m (sym_eq_nat _ _ X)).
  - apply IHm.
    +
Admitted.

Theorem add_O_l: forall m n, EqNat 0 m -> EqNat n (m + n).
Proof.
  intros.
  induction m.
  - simpl.
    apply refl_eq_nat.
  - destruct (false_O_S m X).
Defined.

Print add_O_l.

Theorem add_S_comm: forall m n, EqNat (S m + n) (m + S n).
Proof.
  induction m; intros.
  - simpl.
    apply refl_eq_nat.
  - destruct n.
    + simpl.
      pose proof (IHm 0) as H.
      simpl in H.
      apply inj_eq_nat.
      exact H.
    + simpl.
      apply inj_eq_nat.
      exact (IHm (S n)).
Defined.

Print add_S_comm.

Theorem add_comm: forall m n, EqNat (m + n) (n + m).
Proof.
  induction m; induction n.
  - apply refl_eq_nat.
  - simpl.
    simpl in IHn.
    apply inj_eq_nat.
    exact IHn.
  - simpl.
    simpl in IHm.
    pose proof (IHm 0) as IHm0.
    simpl in IHm0.
    apply inj_eq_nat.
    exact IHm0.
  - simpl.
    apply inj_eq_nat.
    pose proof (IHm (S n)) as IHm_Sn.
    apply trans_eq_nat with (n := S n + m).
    + exact IHm_Sn.
    + apply sym_eq_nat in IHm_Sn.
      apply trans_eq_nat with (n := m + S n).
      * exact IHm_Sn.
      * apply trans_eq_nat with (n := S m + n).
        -- apply sym_eq_nat.
           apply add_S_comm.
        -- exact IHn.
Defined.

Print add_comm.

Theorem square_eq_nat: forall l m n o, EqNat l m -> EqNat l n -> EqNat m o -> EqNat n o.
Proof.
  intros.
  apply trans_eq_nat with (n := l).
  - apply sym_eq_nat.
    exact X0.
  - apply trans_eq_nat with (n := m).
    -- exact X.
    -- exact X1.
Defined.

Print square_eq_nat.

Theorem add_n_r: forall n l m, EqNat l m -> EqNat (l + n) (m + n).
Proof.
  induction n; intros.
  - assert (H': EqNat (0 + l) (0 + m)). {
      simpl.
      exact X.
    }
    apply square_eq_nat with (l := (0 + l)) (m := (0 + m)).
    * exact H'.
    * apply add_comm.
    * apply add_comm.
  - assert (H': EqNat (S l + n) (S m + n)). {
      simpl.
      apply inj_eq_nat.
      apply IHn.
      exact X.
    }
    apply square_eq_nat with (l := (S l + n)) (m := (S m + n)).
    * exact H'.
    * apply add_S_comm.
    * apply add_S_comm.
Defined.

Print add_n_r.

Inductive VecF (A : Type) (n : nat) : Type :=
| nil_f : EqNat 0 n -> VecF A n
| cons_f : A -> forall (m : nat), EqNat (S m) n -> VecF A m -> VecF A n.

Theorem subst_vecF : forall m n A (p : EqNat m n) (v : VecF A m), VecF A n.
Proof.
  intro m.
  induction m.
  - destruct n; intros.
    + exact v.
    + destruct (false_O_S n p).
  - destruct n; intros.
    + apply sym_eq_nat in p.
      destruct (false_O_S m p).
    + pose proof (proj_eq_nat m n p) as H.
      destruct v.
      * destruct (false_O_S m e).
      * pose proof (proj_eq_nat m0 m e) as H'.
        refine (cons_f A (S n) a m0 _ _).
        -- apply trans_eq_nat with (n:= (S m)).
           --- exact e.
           --- exact p.
        -- exact v.
Defined.

Print subst_vecF.

Definition append (A : Type) (m n : nat) (v1 : VecF A m) (v2 : VecF A n)
  : VecF A (m + n).
Proof.
  induction v1.
  - exact (subst_vecF n (n0 + n) A (add_O_l n0 n e) v2).
  - refine (cons_f A (n0 + n) a (m + n) _ IHv1).
    assert (H: EqNat ((S m) + n) (n0 + n)). {
      apply add_n_r.
      exact e.
    }
    simpl in H.
    exact H.
Defined.

Print append.

Definition append' (A : Type) (m n : nat) (v1 : VecF A m) (v2 : VecF A n)
  : VecF A (m + n).
Proof.
  generalize dependent m.
  refine (
      fix F (m: nat) : forall (v1 : VecF A m), VecF A (m + n) :=
        match m as m0 return forall (v1 : VecF A m0), VecF A (m0 + n) with
        | O => fun (v1 : VecF A 0) => v2
        | S m0 => fun (v1 : VecF A (S m0)) =>
                   match v1 as v1' return VecF A (S m0 + n) with
                   | nil_f _ _ e => _
                   | cons_f _ _ hd m e v0 => _
                   end
        end).
  - destruct (false_O_S m0 e).
  - apply (cons_f A (S m0 + n) hd (m0 + n)).
    + apply refl_eq_nat.
    + exact (F m0 (subst_vecF _ _ _ (proj_eq_nat _ _ e) v0)).
Defined.

Print append'.

(*
Theorem append_eq: forall (A : Type) (m n : nat) (v1 : VecF A m) (v2 : VecF A n), append A m n v1 v2 = append' A m n v1 v2.
Proof.
  intros.
  unfold append.
  unfold append'.
  induction m.
  - destruct v1.
    + simpl.
      induction n.
      * reflexivity.
      * simpl.
        destruct v2.
        -- destruct (false_O_S n e0).
        -- simpl.*)

Definition head: forall A n, VecF A (S n) -> A.
Proof.
  intros.
  destruct X.
  - destruct (false_O_S n e).
  - exact a.
Defined.

Print head.

Definition filter_len' A n (f: A -> bool) (v: VecF A n) : nat.
Proof.
  induction v.
  - exact 0.
  - destruct (f a).
    + exact (1 + IHv).
    + exact (0 + IHv).
Defined.

Definition filter_len A n (f: A -> bool) (v: VecF A n) : nat.
Proof.
  refine (
      (fix F (n: nat) : forall (v : VecF A n), nat :=
         match n as n0 return forall (v : VecF A n0), nat with
         | O => fun (v : VecF A 0) => 0
         | S n0 => fun (v : VecF A (S n0)) =>
                    match v with
                    | nil_f _ _ e =>
                        match e with
                        | refl_nat _ _ contr =>
                            match contr return nat with end
                        end
                    | cons_f _ _ hd m e v0 => _
                    end
         end
      )
        n v
    ).
  destruct (f hd) eqn:H.
  - refine (1 + (F n0 _)).
    apply subst_vecF with (m:=m).
    + apply proj_eq_nat.
      exact e.
    + exact v0.
  - refine (F n0 _).
    apply subst_vecF with (m:=m).
    + apply proj_eq_nat.
      exact e.
    + exact v0.
Defined.


Print filter_len.

Example filter_len_ex0 : filter_len _ _ (fun n => n <=? 5)
                           (cons_f _ 2 2 1 (refl_nat 2 2 tt)
                              (cons_f _ _ 1 0 (refl_nat 1 1 tt)
                                 (nil_f _ _ (refl_nat 0 0 tt)))) = 2.
Proof. reflexivity. Defined.

Example filter_len_ex1 : filter_len _ _ (fun n => n <=? 5)
                           (cons_f _ 2 2 1 (refl_nat 2 2 tt)
                              (cons_f _ _ 7 0 (refl_nat 1 1 tt)
                                 (nil_f _ _ (refl_nat 0 0 tt)))) = 1.
Proof. reflexivity. Defined.

Example filter_len_ex2 : filter_len _ _ (fun n => n <=? 5)
                           (cons_f _ 2 12 1 (refl_nat 2 2 tt)
                              (cons_f _ _ 7 0 (refl_nat 1 1 tt)
                                 (nil_f _ _ (refl_nat 0 0 tt)))) = 0.
Proof. reflexivity. Defined.

Print VecF_rect.

Theorem unit_same: forall (t: unit) (P: unit -> Type), P t -> P tt.
Proof.
  intros.
  destruct t.
  exact X.
Defined.

Print unit_same.

(** This definition doesn't work because the return type of fix should be
    something like "forall (m : nat) (v : VecF A m), EqNat m n -> P m v"
    but we can't prove this until we can prove subst_eq_nat *)

Print VecF_rect.

Definition VecF_rect': forall (A : Type) (P : forall n : nat, VecF A n -> Type)
    (f : P 0 (nil_f A 0 (refl_nat 0 0 tt)))
    (f0 : forall (n : nat) (a : A) (v : VecF A n),
        P n v -> P (S n) (cons_f A (S n) a n (refl_eq_nat (S n)) v)),
    (forall n v, P n v).
Proof.
  refine (
      fun (A : Type) (P : forall n : nat, VecF A n -> Type)
        (f : P 0 (nil_f A 0 (refl_nat 0 0 tt)))
        (f0 : forall (n : nat) (a : A) (v : VecF A n),
            P n v -> P (S n) (cons_f A (S n) a n (refl_eq_nat (S n)) v)) =>
        fix F (n : nat) : forall (v : VecF A n), P n v :=
        match n as n0 return forall (v : VecF A n0), P n0 v with
        | O => fun (v : VecF A 0) =>
                match v as v0 return (P 0 v0) with
                | nil_f _ _ e => _
                | cons_f _ _ y m e v0 =>
                    match e with
                    | refl_nat _ _ contr =>
                        match contr return P 0 (cons_f A 0 y m e v0) with end
                    end
                end
        | S n0 => fun (v : VecF A (S n0)) =>
                   match v as v0 return (P (S n0) v0) with
                   | nil_f _ _ e =>
                       match e with
                       | refl_nat _ _ contr =>
                           match contr return P (S n0) (nil_f A (S n0) e) with end
                       end

                   | cons_f _ _ y m e v0 => _
                   end
        end).
  - destruct e.
    destruct e.
    exact f.
  - pose proof (F n0 (subst_vecF m n0 A (proj_eq_nat m n0 e) v0)) as H''.
    pose proof (f0 n0 y (subst_vecF m n0 A (proj_eq_nat m n0 e) v0) H'') as H'.
Admitted.

Definition filter' A n (f: A -> bool) (v: VecF A n) : VecF A (filter_len' A n f v).
Proof.
  induction v.
  - apply nil_f.
    constructor.
    unfold eq_nat.
    simpl.
    destruct n.
    + exact tt.
    + destruct e.
      unfold eq_nat in e.
      destruct e.
  - destruct (f a) eqn:Eq.
    + apply cons_f with (m:= filter_len' A m f v).
      -- exact a.
      -- simpl. rewrite Eq. apply refl_eq_nat.
      -- exact IHv.
    + simpl. rewrite Eq. exact IHv.
Defined.

Print filter'.

Lemma filter_len_eq: forall A f n m (e: EqNat m n) v,
    EqNat (filter_len A n f (subst_vecF m n A e v))
      (filter_len A m f v).
Proof.
  intros A f.
  refine (fix F (n': nat) : forall m e0 v2,
             EqNat (filter_len A n' f (subst_vecF m n' A e0 v2))
               (filter_len A m f v2) :=
            match n' as n' return (forall m e0 v2,
                                      EqNat (filter_len A n' f
                                               (subst_vecF m n' A e0 v2))
                                        (filter_len A m f v2)) with
            | O => fun m e v =>
                    match v with
                    | nil_f _ _ e => _
                    | cons_f _ _ y m e v0 => _
                    end
            | S n'' => fun m e v =>
                        match v with
                        | nil_f _ _ e => _
                        | cons_f _ _ y m e v0 => _
                        end
            end
         ).
  - pose proof (F 0 m e0 (nil_f A m e)) as H.
    apply trans_eq_nat with (n:=(filter_len A m f (nil_f A m e))).
    + exact H.
    + simpl.
      constructor.
      apply refl_eq_nat.
  - assert (contr: EqNat (S m) 0). {
      apply trans_eq_nat with (n:=m0).
      + exact e.
      + exact e0.
    }
    destruct (false_O_S m).
    exact (sym_eq_nat (S m) 0 contr).
  - assert (contr: EqNat 0 (S n'')). {
      apply trans_eq_nat with (n:=m).
      + exact e.
      + exact e0.
    }
    destruct (false_O_S n'').
    exact contr.
  - simpl.
    destruct m0.
    -- destruct (false_O_S n'' e0).
    -- destruct (subst_vecF (S m0) (S n'') A e0 (cons_f A (S m0) y m e v0)) eqn:Eq.
      + destruct (false_O_S n'' e1).
      + simpl. destruct (f a).
      * pose proof (F n'' m1 (proj_eq_nat m1 n'' e1) v1) as H.
    (*assert (H: EqNat (S m) (S n'')). {
      apply trans_eq_nat with (n:=m0).
      + exact e.
      + apply proj_eq_nat.
        exact e0.
    }
    assert (H': EqNat (S n'') m). {

    }
    pose proof (F n'' m H (cons_f A m y n'' e v0)) as H.*)
    Admitted.

(* Defining equality of forded vectors *)
(*
Definition eq_vec_nat (n : nat) (u v : VecF A n) : Type :=
  match u with
  | nil_f _ _ e => match v with
                  | nil_f _ _ e' => Unit
                  | cons_f _ _ hd m e' tl => Void
                  end
  | cons_f _ _ hd m e => match

Inductive EqVecNat (n : nat) (u v : VecF A n) : Type :=
  refl_vec_nat:
*)

Definition filter A n (f: A -> bool) (v: VecF A n) : VecF A (filter_len A n f v).
Proof.
  refine (
      (fix F (n: nat) : forall (v : VecF A n), VecF A (filter_len A n f v) :=
         match n as n0 return forall (v : VecF A n0), VecF A (filter_len A n0 f v) with
         | O => fun (v : VecF A 0) =>
                 match v as v0 return VecF A (filter_len A 0 f v0) with
                 | nil_f _ _ e => nil_f _ _ e
                 | cons_f _ _ y m e v0 =>
                     match e with
                     | refl_nat _ _ contr =>
                         match contr return VecF A (filter_len A 0 f (cons_f A 0 y m e v0)) with end
                     end
                 end
         | S n0 => fun (v : VecF A (S n0)) =>
                    match v as v0 return VecF A (filter_len A (S n0) f v0) with
                    | nil_f _ _ e =>
                        match e with
                        | refl_nat _ _ contr =>
                            match contr return VecF A (filter_len A (S n0) f (nil_f A (S n0) e)) with end
                        end

                    | cons_f _ _ hd m e v0 => _
                    end
         end
      )
        n v
    ).
  simpl.
  destruct (f hd).
  - apply cons_f with (m:= filter_len A m f v0).
    + exact hd.
    + apply inj_eq_nat.
      apply (sym_eq_nat).
      apply (filter_len_eq).
    + apply subst_vecF with (m := (filter_len A n0 f (subst_vecF m n0 A (proj_eq_nat m n0 e) v0))).
      * apply filter_len_eq.
      * apply F.
  (*exact (subst_vecF _ _ _
               (filter_len_eq _ _ _ _ e v0)
               (F n0 (subst_vecF m n0 A (proj_eq_nat m n0 e) v0))).*)
  - apply subst_vecF with (m := (filter_len A n0 f (subst_vecF m n0 A (proj_eq_nat m n0 e) v0))).
      * apply refl_eq_nat.
      * apply F.
Defined.

(*Inductive EqVecF (A : Type) (v1 v2: VecF A n) : Type :=*)


Example filter_ex0 : filter _ _ (fun n => n <=? 5)
                           (cons_f _ 2 2 1 (refl_nat 2 2 tt)
                              (cons_f _ _ 1 0 (refl_nat 1 1 tt)
                                 (nil_f _ _ (refl_nat 0 0 tt))))
                     =
                       (cons_f _ 2 2 1 (refl_nat 2 2 tt)
                          (cons_f _ _ 1 0 (refl_nat 1 1 tt)
                             (nil_f _ _ (refl_nat 0 0 tt)))).
Proof. simpl. Admitted.

Example filter_ex1 : filter _ _ (fun n => n <=? 3)
                           (cons_f _ 2 3 1 (refl_nat 2 2 tt)
                              (cons_f _ _ 5 0 (refl_nat 1 1 tt)
                                 (nil_f _ _ (refl_nat 0 0 tt))))
                     =
                       (cons_f _ _ 3 0 (refl_nat 1 1 tt)
                          (nil_f _ _ (refl_nat 0 0 tt))).
Proof. simpl. Admitted.

Compute filter _ _ (fun n => n <=? 3)
  (cons_f _ 2 3 1 (refl_nat 2 2 tt)
     (cons_f _ _ 5 0 (refl_nat 1 1 tt)
        (nil_f _ _ (refl_nat 0 0 tt)))).

Inductive FinF (n : nat) : Type :=
  | fzero: forall m, EqNat (S m) n -> FinF n
  | fsucc: forall m, FinF m -> EqNat (S m) n -> FinF n.

Lemma false_fin_O : forall (n : FinF 0), Empty_set.
Proof.
  intros.
  destruct n.
  - apply (false_O_S m (sym_eq_nat _ _ e)).
  - apply (false_O_S m (sym_eq_nat _ _ e)).
Defined.

Print false_fin_O.

Lemma subst_finF : forall m n, EqNat m n -> FinF m -> FinF n.
Proof.
  induction m.
  - destruct n; intros.
    + exact X0.
    + destruct (false_O_S n X).
  - destruct n; intros.
    + destruct (false_O_S m (sym_eq_nat _ _ X)).
    + destruct X0.
      * exact (fzero (S n) n (refl_eq_nat _)).
      * exact (fsucc (S n) m0 X0 (trans_eq_nat _ _ _ e X)).
Defined.

Print subst_finF.

Definition nthF A :=
  fix F (n : nat) : forall (v : VecF A n), FinF n -> A :=
    match n as n0 return forall (v : VecF A n0), FinF n0 -> A with
    | 0 => fun v : VecF A 0 =>
            fun i : FinF 0 => match false_fin_O i with end
    | S n' => fun v : VecF A (S n') =>
            match v as v0 return FinF (S n') -> A with
            | nil_f _ _ e => fun i : FinF (S n') =>
                              match (false_O_S n' e) with end

            | cons_f _ _ hd m e v0 =>
                fun i : FinF (S n') =>
                  match i return VecF A n' -> A with
                  | fzero _ _ _ => fun _ => hd
                  | fsucc _ o p e' => fun v' => F n' v' (subst_finF _ _ (proj_eq_nat _ _ e') p)
                  end (subst_vecF _ _ A (proj_eq_nat _ _ e) v0)
            end
    end.

Print nthF.

Example nthF_ex1 : nthF nat 2 (cons_f _ 2 2 1 (refl_nat 2 2 tt)
                              (cons_f _ _ 1 0 (refl_nat 1 1 tt)
                                 (nil_f _ _ (refl_nat 0 0 tt))))
                         (fsucc 2 1 (fzero 1 0 (refl_nat 1 1 tt)) (refl_nat 2 2 tt))
                    = 1.
Proof. reflexivity. Qed.

Example nthF_ex2 : nthF nat 3 (cons_f _ 3 4 2 (refl_nat 3 3 tt)
                               (cons_f _ _ 5 1 (refl_nat 2 2 tt)
                                  (cons_f _ _ 6 0 (refl_nat 1 1 tt)
                                     (nil_f _ _ (refl_nat 0 0 tt)))))
                         (fsucc 3 2 (fzero 2 1 (refl_nat 2 2 tt)) (refl_nat 3 3 tt))
                    = 5.
Proof. reflexivity. Qed.

Inductive List (A : Type) : Type :=
| nil: List A
| cons: A -> List A -> List A.

Fixpoint length (A: Type) (l : List A) : nat :=
  match l with
  | nil _ => 0
  | cons _ hd tl => S (length A tl)
  end.

Inductive Vec' (A : Type) (n : nat) : Type :=
    pair: forall (l : List A), EqNat n (length A l) -> Vec' A n.
